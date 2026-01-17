# 分离逻辑验证中的精确性问题分析

## 问题概述

在验证 List Box（`sllb`）相关函数时，遇到了分离逻辑中的**精确性问题（Precision Problem）**。核心问题是：**当谓词转换链中存在会丢失尾指针 `pt` 信息的步骤时，无法在函数返回时重建需要精确 `pt` 值的原始谓词**。

本文档分析了两种验证策略的成功与失败案例，阐明了谓词组合选择的设计原理。

## 问题本质

精确性问题的根源：**存在量化变量在谓词转换过程中失去与原始具体值的联系**。

具体表现为：
1. 初始状态有精确的 `pt` 值（例如通过 C 变量 `box->ptail` 读取）
2. 转换为 `sll` 或 `sllseg` 时，`pt` 信息被丢弃
3. 函数返回时，使用引理重建 `sllbseg` 会引入**新的存在量化变量** `pt_new`
4. 无法证明 `pt_new = pt`（原始值），因为 `pt` 的信息已经在转换中丢失

## 成功案例：`app_list_box` - 精确跟踪模式

### 函数规约

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
  struct sll *h2 = b2->head;        // 显式读取到 C 变量
  struct sll **pt2 = b2->ptail;     // 显式读取到 C 变量
  *(b1->ptail) = h2;
  if (h2 != (struct sll *)0) {
    b1->ptail = pt2;                // 使用具体的 C 变量
  }
  free_sllb(b2);
  return b1;
}
```

### 成功关键

1. **`which implies` 显式引入存在变量 `pt1, h2, pt2`**
   - 立即通过 C 赋值语句将它们绑定到具体值
   - `h2 = b2->head` 和 `pt2 = b2->ptail` 使得后续可以直接使用这些 C 变量

2. **不调用会丢失 `pt` 的子函数**
   - 直接指针操作，没有循环遍历
   - 不需要转换为 `sll` 或 `sllseg`
   - 全程保持 `sllbseg` + `sll_pt` 结构

3. **使用保持精确性的引理重建 `sllb`**
   - `sllbseg_append_sllbseg`：合并链表段，所有 `pt` 值都是明确的 C 变量
   - `sllbseg_2_sllb`：从 `sllbseg` 重建 `sllb`，使用具体的 `pt` 值

### 验证结果

所有证明都是 `Qed`（完全验证），无 `Admitted`：
- `proof_of_app_list_box_which_implies_wit_1` ✓
- `proof_of_app_list_box_return_wit_1` ✓
- `proof_of_app_list_box_return_wit_2` ✓

## 挑战案例：`sllb2array` - 精确性陷阱

### 问题场景

如果 `sllb2array` 尝试使用 `sllbseg` 谓词并保持 `pt` 跟踪：

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

### 精确性陷阱

1. **必须转换为 `sll` 才能调用 `sll2array`**
   - `sll2array` 规约使用 `sll(head, l)`
   - 转换过程：`sllbseg(..., pt, l)` → `sll(h, l)`
   - **`pt` 信息在此丢失**

2. **内部 `sll2array` 使用 `sll` 和 `sllseg`**
   - 循环不变量：`sllseg(..., l1) * sll(..., l2)`
   - 遍历过程完全不涉及尾指针跟踪

3. **返回时无法重建原始 `sllbseg`**
   - 只能使用引理：`sll h l |-- EX pt_new, sllbseg(..., pt_new, l)`
   - `pt_new` 是**新引入的存在变量**，与原始 `pt` 无关
   - 无法证明 `pt_new = pt`，因为 `pt` 的值已在转换中丢失

### 为何无法修复

**缺失的引理**（无法证明）：

```coq
Lemma sll_to_sll_pt_preserve: forall h pt l,
  sll h l |-- sll_pt h pt l.  (* 无法证明：sll 不包含 pt 信息 *)
```

这个引理无法证明，因为：
- `sll h l` 只描述链表结构，不包含任何关于尾指针位置的信息
- `sll_pt h pt l` 需要额外的 `pt` 信息
- 在没有额外资源的情况下，无法从 `sll` 推导出具体的 `pt` 值

## 解决方案：两套谓词组合策略

### 策略 1：精确跟踪模式（`sll_pt` + `sllb/sllbseg`）

**适用场景**：需要保留尾指针信息以完成**链表连接**操作

**应用函数**：
- `cons_list` - 使用 `sll_pt`，返回新的尾指针位置
- `cons_list_box` - 使用 `sllbseg`，调用 `cons_list`
- `app_list_box` - 使用 `sllb`，展开为 `sllbseg` + `sll_pt`

**核心原则**：
1. 通过 `which implies` 显式引入 `pt` 变量
2. 立即读取到 C 变量，绑定具体值
3. 避免调用会丢失 `pt` 的子函数（如带 `sll` 循环的函数）
4. 全程保持 `sllbseg`/`sll_pt` 结构
5. 使用保持精确性的引理完成验证

### 策略 2：宽松遍历模式（`sll` + `sllb_sll`）

**适用场景**：只读遍历、转换或不需要后续连接的操作

**应用函数**：
- `map_list` - 使用 `sll`
- `map_list_box` - 使用 `sllb_sll`，调用 `map_list`
- `sll2array` - 使用 `sll`
- `sllb2array` - 使用 `sllb_sll`，调用 `sll2array`
- `free_list_box` - 使用 `sllb`（在 `which implies` 中转换为 `sll`）

**核心原则**：
1. 使用 `sllb_sll` **主动放弃尾指针跟踪**
2. 内部调用使用 `sll` 规约的函数，谓词转换链路清晰
3. 避免精确性问题，因为从一开始就不跟踪 `pt`
4. **代价**：无法在函数返回后进行链表连接操作
5. **收益**：既然目标是转数组/释放/只读操作，不需要后续连接是可接受的

### 设计权衡

| 方面 | 精确跟踪模式 | 宽松遍历模式 |
|------|-------------|-------------|
| **谓词** | `sllb`, `sllbseg`, `sll_pt` | `sllb_sll`, `sll`, `sllseg` |
| **尾指针** | 精确跟踪具体值 | 放弃跟踪（设为 0） |
| **适用操作** | 链表连接、结构修改 | 只读遍历、转换、释放 |
| **能调用子函数** | 仅限保持 `pt` 的函数 | 任何 `sll` 规约的函数 |
| **验证复杂度** | 需要手动证明 | 部分可全自动验证 |
| **后续连接** | 可以 | 不可以 |

## 关键引理

### 精确跟踪模式使用的引理

```coq
(* 展开 sllb 为 sllbseg，暴露尾指针 *)
Lemma sllb_2_sllbseg: forall b l,
  sllb b l |-- EX pt, sllbseg(&(b->head), pt, l) ** store(pt, 0).

(* 从 sll_pt 提取尾指针信息 *)
Lemma sllb_2_sll_pt: forall b l,
  sllb b l |-- EX h pt, store(&(b->head), h) ** sll_pt h pt l.

(* 连接两个链表段，保持尾指针精确性 *)
Lemma sllbseg_append_sllbseg: forall x pt1 l1 h2 pt2 z l2,
  sllbseg x pt1 l1 ** store(pt1, h2) ** sll_pt h2 pt2 l2 |--
  sllbseg x pt2 (l1 ++ z :: l2).

(* 重建 sllb，使用具体的 pt 值 *)
Lemma sllbseg_2_sllb: forall b pt l,
  store(&(b->ptail), pt) ** sllbseg(&(b->head), pt, l) ** store(pt, 0) |--
  sllb b l.
```

### 宽松遍历模式使用的引理

```coq
(* 展开 sllb_sll 为 sll *)
Lemma sllb_sll_2_sll: forall b l,  (* Strategy 35 *)
  sllb_sll b l |-- EX h, store(&(b->head), h) ** sll h l.

(* 从 sll 重建 sllb_sll *)
Lemma sll_2_sllb_sll: forall b l,  (* Strategy 36 *)
  EX h, store(&(b->head), h) ** sll h l |-- sllb_sll b l.
```

## 总结

精确性问题的核心教训：

1. **明确目标**：函数是否需要后续连接操作？
   - 需要 → 使用精确跟踪模式
   - 不需要 → 使用宽松遍历模式

2. **谓词一致性**：保持整个调用链的谓词系统一致
   - 精确模式：全程使用 `sllbseg`/`sll_pt`，避免转换为 `sll`
   - 宽松模式：从一开始使用 `sllb_sll`，匹配内部 `sll` 函数

3. **权衡代价**：
   - 精确模式：验证更复杂，但保留完整功能
   - 宽松模式：验证更简单（部分全自动），但放弃连接能力

4. **实用主义**：对于 `sllb2array` 这样的函数，目标是转换为数组，后续不需要链表连接，因此使用宽松模式是合理的设计选择。
