# 分离逻辑验证中的精确性问题分析

## 问题概述

在验证 List Box（`sllb`）相关函数时，我们遇到了分离逻辑中的精确性问题。问题的核心在于：当谓词转换链中存在会丢失尾指针 `pt` 信息的步骤时，我们无法在函数返回时重建需要精确 `pt` 值的原始谓词。这个问题的根源是存在量化变量在谓词转换过程中失去了与原始具体值的联系。

考虑一个典型的场景：初始状态下我们有精确的 `pt` 值（通过 C 变量 `box->ptail` 读取），但当转换为 `sll` 或 `sllseg` 时，`pt` 信息被丢弃。函数返回时，使用引理重建 `sllbseg` 会引入新的存在量化变量 `pt_new`，而我们无法证明 `pt_new = pt`，因为原始 `pt` 的信息已经在转换中丢失了。

## 成功案例：`app_list_box`

`app_list_box` 的验证完全成功，没有任何 `Admitted`。这个函数将两个 List Box 合并，要求在返回时保持精确的 `sllb` 谓词。

```c
struct sllb *app_list_box(struct sllb *b1, struct sllb *b2)
/*@ With l1 l2
    Require sllb(b1, l1) * sllb(b2, l2)
    Ensure sllb(__return, app(l1, l2))
*/
{
  /*@ sllb(b1, l1) * sllb(b2, l2)
      which implies
      exists pt1 h2 pt2,
          store(&(b1 -> ptail), pt1) *
          sllbseg(&(b1 -> head), pt1, l1) * store(pt1, 0) *
          store(&(b2 -> head), h2) * store(&(b2 -> ptail), pt2) *
          sll_pt(h2, pt2, l2)
  */
  struct sll *h2 = b2->head;
  struct sll **pt2 = b2->ptail;
  *(b1->ptail) = h2;
  if (h2 != (struct sll *)0) {
    b1->ptail = pt2;
  }
  free_sllb(b2);
  return b1;
}
```

成功的关键在于三点。首先，`which implies` 子句显式引入了存在变量 `pt1`、`h2` 和 `pt2`，这些变量立即通过 C 赋值语句绑定到具体值。其次，函数本身不调用任何会丢失 `pt` 的子函数——所有操作都是直接的指针操作，全程保持 `sllbseg` 和 `sll_pt` 结构。最后，重建 `sllb` 时使用的引理（`sllbseg_append_sllbseg` 和 `sllbseg_2_sllb`）都能保持精确性，因为所有 `pt` 值都是明确的 C 变量。

## 挑战案例：`sllb2array`

相比之下，如果 `sllb2array` 尝试保持 `pt` 跟踪就会陷入精确性陷阱。

```c
unsigned int sllb2array(struct sllb *box, unsigned int **out_array)
/*@ With l pt
    Require sllbseg(&(box->head), pt, l) * store(pt, 0) * ...
    Ensure sllbseg(&(box->head), pt_new, l) * store(pt_new, 0) * ...
*/
{
  /*@ which implies exists h, store(&(box->head), h) * sll(h, l) */
  return sll2array(box->head, out_array);
}
```

问题在于 `sllb2array` 必须调用 `sll2array`，而 `sll2array` 的规约使用 `sll(head, l)`。这意味着我们必须将 `sllbseg(..., pt, l)` 转换为 `sll(h, l)`，而在这个转换过程中 `pt` 信息被丢弃了。更糟糕的是，`sll2array` 内部的循环不变量使用 `sllseg(..., l1) * sll(..., l2)`，整个遍历过程完全不涉及尾指针跟踪。函数返回时，我们只能使用引理 `sll h l |-- EX pt_new, sllbseg(..., pt_new, l)` 来重建 `sllbseg`，但这里的 `pt_new` 是新引入的存在变量，与原始的 `pt` 毫无关系。这个问题无法通过技巧解决，我们需要一个引理 `sll h l |-- sll_pt h pt l`，但这在没有额外资源的情况下无法证明，因为 `sll` 根本不包含关于尾指针位置的任何信息。

## 解决方案：两套谓词组合

基于上述分析，我们设计了两套谓词组合策略。

**精确跟踪模式**使用 `sll_pt`、`sllb` 和 `sllbseg` 谓词，适用于需要后续连接操作的函数，如 `cons_list`、`cons_list_box` 和 `app_list_box`。这些函数必须通过 `which implies` 显式引入尾指针变量，并立即读取到 C 变量中绑定具体值。关键在于全程保持 `sllbseg`/`sll_pt` 结构，避免调用会丢失尾指针信息的子函数（如带 `sll` 循环的函数），并使用保持精确性的引理完成验证。

**宽松遍历模式**则主动放弃尾指针跟踪，使用 `sllb_sll` 和 `sll` 谓词。这种模式适用于只读遍历、转换或不需要后续连接的操作，如 `map_list`、`sll2array`、`sllb2array` 和 `free_list_box`。通过一开始就不跟踪尾指针，完全避免了精确性问题。代价是无法在函数返回后进行链表连接，但对于转数组、释放或只读操作来说，这是可接受的。内部可以安全调用任何使用 `sll` 规约的函数，谓词转换链路清晰，部分验证甚至可以全自动完成。

两种策略的权衡体现在多个方面：精确跟踪模式使用 `sllb`、`sllbseg`、`sll_pt` 谓词，精确跟踪尾指针的具体值，适用于链表连接和结构修改操作，但只能调用保持尾指针的函数，验证需要手动证明；宽松遍历模式使用 `sllb_sll`、`sll`、`sllseg` 谓词，直接将尾指针设为 0 放弃跟踪，适用于只读遍历、转换和释放操作，可以调用任何 `sll` 规约的函数，部分可全自动验证，但无法支持后续连接。

## 关键引理

精确跟踪模式依赖一组保持尾指针精确性的引理。`sllb_2_sllbseg` 和 `sllb_2_sll_pt` 用于展开 `sllb` 并暴露尾指针，`sllbseg_append_sllbseg` 是连接两个链表段的核心引理，而 `sllbseg_2_sllb` 则用于重建 `sllb` 谓词。这些引理都要求 `pt` 值是具体的，而不是存在量化的。

```coq
Lemma sllb_2_sllbseg: forall b l,
  sllb b l |-- EX pt, sllbseg(&(b->head), pt, l) ** store(pt, 0).

Lemma sllb_2_sll_pt: forall b l,
  sllb b l |-- EX h pt, store(&(b->head), h) ** sll_pt h pt l.

Lemma sllbseg_append_sllbseg: forall x pt1 l1 h2 pt2 z l2,
  sllbseg x pt1 l1 ** store(pt1, h2) ** sll_pt h2 pt2 l2 |--
  sllbseg x pt2 (l1 ++ z :: l2).

Lemma sllbseg_2_sllb: forall b pt l,
  store(&(b->ptail), pt) ** sllbseg(&(b->head), pt, l) ** store(pt, 0) |--
  sllb b l.
```

宽松遍历模式则使用 Strategy 35 和 36，它们在 `sllb_sll` 和 `sll` 之间进行转换，完全不涉及尾指针跟踪。

```coq
Lemma sllb_sll_2_sll: forall b l,
  sllb_sll b l |-- EX h, store(&(b->head), h) ** sll h l.

Lemma sll_2_sllb_sll: forall b l,
  EX h, store(&(b->head), h) ** sll h l |-- sllb_sll b l.
```

## 总结

精确性问题的核心是理解函数的目标。如果需要后续连接，就必须精确跟踪尾指针，通过 `which implies` 显式引入并使用支持精确性的引理；如果只是遍历、转换或释放，主动放弃跟踪反而简化验证。谓词选择直接决定了验证策略和可调用函数的范围，理解这一点是成功完成 List Box 验证的关键。
