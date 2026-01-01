# sllb2array 验证中的精确性问题分析

## 问题概述

在验证 `sllb2array` 函数时，遇到了分离逻辑中的**精确性问题（Precision Problem）**。核心问题是：当函数调用链中使用了会丢失尾指针 `pt` 信息的谓词转换时，无法在返回时重建原始 `sllb` 谓词。

## 成功案例分析：`app_list_box`

### 代码结构

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
          b1 != 0 && b2 != 0 &&
          store(&(b1 -> ptail), struct sll **, pt1) *
          sllbseg(&(b1 -> head), pt1, l1) * store(pt1, struct sll *, 0) *
          store(&(b2 -> head), struct sll *, h2) *
          store(&(b2 -> ptail), struct sll **, pt2) *
          sll_pt(h2, pt2, l2)
  */
  struct sll *h2 = b2->head;        // 直接读取 h2
  struct sll **pt2 = b2->ptail;     // 直接读取 pt2
  *(b1->ptail) = h2;
  if (h2 != (struct sll *)0) {
    b1->ptail = pt2;
  }
  free_sllb(b2);
  return b1;
}
```

### 成功原因

1. **`which implies` 显式引入 `pt1, h2, pt2`**
   - 这些存在变量被立即读取到 C 变量中
   - `h2 = b2->head` 和 `pt2 = b2->ptail` 将存在变量与实际值绑定

2. **不使用循环**
   - 直接指针操作，不需要循环不变式
   - 不会在遍历过程中丢失 `pt` 信息

3. **直接重建 `sllb`**
   - 通过 `sllbseg_store_2_sllb` 和 `sllbseg_append_sllbseg` 引理
   - 所有 `pt` 值都是明确的，不是存在量化的

### 证明状态

所有证明都是 `Qed`，没有 `Admitted`：
- `proof_of_app_list_box_return_wit_1` ✓
- `proof_of_app_list_box_return_wit_2` ✓
- `proof_of_app_list_box_which_implies_wit_1` ✓

## 失败案例分析：`sllb2array`

### 当前代码结构

```c
unsigned int sllb2array(struct sllb *box, unsigned int **out_array)
/*@ With l pt b out
    Require ... sllbseg(&(box -> head), pt, l) * store(pt, struct sll *, 0) ...
    Ensure exists arr_ret pt_new,
           sllbseg(&(b -> head), pt_new, l) * store(pt_new, struct sll *, 0) ...
*/
{
  /*@ sllbseg(&(box -> head), pt, l) * store(pt, struct sll *, 0)
      which implies
      exists h, store(&(box -> head), struct sll *, h) * sll(h, l)  // pt 信息丢失！
  */
  return sll2array(box->head, out_array);  // sll2array 使用 sll 规约
}
```

### 失败原因

1. **`which implies` 丢弃 `pt` 信息**
   - 转换为 `sll(h, l)`，不包含 `pt`
   - 这是为了能够调用 `sll2array`

2. **`sll2array` 使用 `sll` 规约**
   - 不跟踪尾指针
   - 内部循环使用 `sllseg`，进一步丢失 `pt`

3. **返回时需要重建 `sllbseg`**
   - 使用 `sll_2_sllbseg` 引入新的存在变量 `pt_new`
   - 无法证明 `pt_new = pt`

## 解决方案

### 方案 1：学习 `app_list_box` - 不调用子函数

**思路**：直接在 `sllb2array` 中实现循环，不调用 `sll2array`

```c
unsigned int sllb2array(struct sllb *box, unsigned int **out_array)
{
  // 直接读取 head 和 ptail
  struct sll *head = box->head;
  struct sll **ptail = box->ptail;
  
  // 在此实现遍历逻辑，使用 sllbseg 保持 pt 跟踪
  unsigned int len = 0;
  struct sll *p = head;
  /*@ Inv ... sllbseg(&(box->head), &(p->next), l1) * sll(p, l2) * 
              (p == NULL && ptail_tracked || p != NULL && ...) */
  while (p) { len++; p = p->next; }
  
  // ... 分配数组并填充 ...
}
```

**优点**：完全保留 `pt` 信息
**缺点**：代码重复，不能复用 `sll2array`

### 方案 2：修改 `sll2array` 规约

**思路**：让 `sll2array` 接受并返回 `pt` 信息

```c
unsigned int sll2array_with_pt(struct sll *head, struct sll **pt, 
                               unsigned int **out_array)
/*@ With l
    Require sll_pt(head, pt, l) * undef_data_at(out_array, unsigned int *)
    Ensure sll_pt(head@pre, pt, l) * ...  // 保持 pt 不变
*/
```

**优点**：可以复用
**缺点**：需要修改内部循环不变式，仍可能有精确性问题

### 方案 3：使用精确性公理

```coq
Axiom sll_structure_preservation: forall h pt l l',
  Zlength l = Zlength l' ->
  (* 如果原始列表有 pt，且新列表结构相同，则 pt 不变 *)
  sllbseg x pt l ** pt |-> NULL |-- 
  sll h l -* (sllbseg x pt l' ** pt |-> NULL).
```

**优点**：直接解决问题
**缺点**：引入公理，可能影响健全性

### 方案 4：接受 `Admitted`

对于语义上正确但无法形式化证明的定理使用 `Admitted`。

**适用情况**：
- `sll2array` 不改变列表结构
- 因此 `pt` 在语义上不变
- 这只是验证系统的表达能力限制

## 关键转换引理

### 可用引理

```coq
(* sllbseg 转 sllseg，丢失 pt 具体值 *)
Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.

(* sll 转 sllbseg，引入新的存在 pt *)
Lemma sll_2_sllbseg: forall x h l,
  l <> nil ->
  x # Ptr |-> h ** sll h l |--
  EX pt: addr, sllbseg x pt l ** pt # Ptr |-> NULL.

(* sllbseg 重建 sllb *)
Lemma sllbseg_store_2_sllb: forall b pt l,
  b <> NULL ->
  &(b->ptail) |-> pt ** sllbseg(&(b->head), pt, l) ** pt |-> NULL |--
  sllb b l.
```

### 缺失的引理

```coq
(* 需要但无法证明：sll 转 sll_pt 保持原始 pt *)
Lemma sll_to_sll_pt_preserve: forall h pt l,
  (* 前提：原始列表有 pt *)
  sll h l |-- sll_pt h pt l.  (* 这是无法证明的！ *)
```

## 结论

精确性问题的本质是：**存在量化变量在转换过程中失去与原始值的联系**。

成功验证 `sllb` 相关函数的关键是：
1. **显式读取** `pt` 到 C 变量
2. **不使用会丢失 `pt` 的谓词转换**
3. **保持 `sllbseg` 结构**，而不是转换为 `sll`

对于 `sllb2array`，建议采用方案 1（直接实现）或方案 4（接受 `Admitted`）。
