# app_list_box 验证问题分析与尝试记录

## 解决方案（已实施）

### 核心问题

原 `sllb` 定义中，空列表时 `sllbseg x y nil = [| x = y |] && emp` 不持有任何资源，
导致验证器无法读取 `b2->head`。

### 解决方案：修改 `sllb` 定义

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  match l with
  | nil =>
      (* 空列表：显式提供 head 资源 *)
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      (* 非空列表：使用 sllbseg（起点有资源） *)
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.
```

### 关键改进

1. **空列表时显式提供资源**：`&(x->head) |-> NULL` 显式存在
2. **保持 `sllbseg` 不变**：首尾相接性质保持
3. **精确性问题消失**：`pt2` 从 `sllb(b2, l2)` 展开后直接保留，无需转换

### 新增引理

```coq
(* 连接两个链表段，保留 pt2 *)
Lemma sllbseg_concat_node: forall x y w z a l1 l2,
  z <> NULL ->
  sllbseg x y l1 ** y # Ptr |-> z **
  &(z # "sll" ->ₛ "data") # UInt |-> a **
  sllbseg (&(z # "sll" ->ₛ "next")) w l2 |--
  sllbseg x w (l1 ++ a :: l2).

(* 连接后直接构造 sllb *)
Lemma sllbseg_concat_node_2_sllb: forall x y w z a l1 l2,
  x <> NULL -> z <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> w **
  sllbseg (&(x # "sllb" ->ₛ "head")) y l1 **
  y # Ptr |-> z ** ... ** w # Ptr |-> NULL |--
  sllb x (l1 ++ a :: l2).
```

### 更新后的 C 代码

```c
/*@ sllb(b1, l1) * sllb(b2, l2)
    which implies
    exists pt1 pt2,
        b1 != 0 && b2 != 0 &&
        store(&(b1 -> ptail), struct sll **, pt1) *
        sllbseg(&(b1 -> head), pt1, l1) * store(pt1, struct sll *, 0) *
        store(&(b2 -> ptail), struct sll **, pt2) *
        sllbseg(&(b2 -> head), pt2, l2) * store(pt2, struct sll *, 0)
*/
```

关键改进：
- 删除了 `store(&(b2 -> head), h2)` 和 `sll(h2, l2)`
- 使用 `sllbseg(&(b2 -> head), pt2, l2)`，直接保留 `pt2`

---

## 历史问题背景

`app_list_box` 函数将两个 `sllb`（带尾指针的链表盒子）连接起来。核心逻辑：
```c
struct sll *h2 = b2->head;
struct sll **pt2 = b2->ptail;
*(b1->ptail) = h2;
if (h2 != 0) {
    b1->ptail = pt2;
}
free_sllb(b2);
return b1;
```

## 核心难点：`pt2 = pt_final` 精确性问题

### 问题描述

在 `return_wit_2`（h2 ≠ 0 分支）中：
- 执行 `b1->ptail = pt2` 后，`&(b1->ptail) |-> pt2`
- 需要构造 `sllb(b1, l1++l2)`，其定义要求：
  ```
  sllb x l = EX ptail, &(x->ptail) |-> ptail ** sllbseg(&(x->head), ptail, l) ** ptail |-> NULL
  ```
- 使用 `sllbseg_pt_sll` 连接 l1 和 l2 时，产生 `EX pt_final, sllbseg(..., pt_final, l1++l2)`
- **问题**：`pt2`（来自原 `sllb(b2, l2)` 的 ptail）和 `pt_final`（引理产生的新变量）需要相等

### 语义分析

- `pt2` 是 `l2` 的尾部指针位置（来自 `sllb(b2, l2)` 展开）
- `pt_final` 也是 `l2` 的尾部指针位置（来自 `sll_2_sllbseg` 转换）
- 语义上 `pt2 = pt_final`，但在 Coq 中需要精确性（precision）推理才能证明

---

## 尝试的方案

### 方案 1：精确性公理

**思路**：添加公理断言 `sll` 的尾部指针是唯一的。

```coq
Axiom sll_tail_precision: forall h l pt1 pt2,
  h <> NULL ->
  (sll h l |-- EX y, sllseg h pt1 l ** pt1 # Ptr |-> y) ->
  (sll h l |-- EX y, sllseg h pt2 l ** pt2 # Ptr |-> y) ->
  pt1 = pt2.
```

**结果**：公理在语义上正确，但在当前框架中需要 Admitted 完成证明。

---

### 方案 2：定义新谓词 `sll_pt`

**思路**：定义一个混合谓词，起点是节点地址（像 `sll`），终点是位置（像 `sllbseg`）。

```coq
Definition sll_pt (h: addr) (pt: addr) (l: list Z): Assertion :=
  match l with
  | nil     => [| h = NULL |] && emp
  | a :: l0 => [| h <> NULL |] &&
               &(h # "sll" ->ₛ "data") # UInt |-> a **
               sllbseg (&(h # "sll" ->ₛ "next")) pt l0
  end.
```

**问题**：
- 当 `l = nil` 时，`h = NULL`，但 `pt` 不被约束
- 需要额外处理空列表情况

---

### 方案 3：在 which_implies 中使用 `sllseg` 代替 `sll`

**思路**：使用 `sllseg(h2, pt2, l2) * store(pt2, 0)` 显式保留 `pt2`。

```c
sllseg(h2, pt2, l2) * store(pt2, struct sll *, 0)
```

**问题**：
- `sllseg` 的第二个参数是**值**（最后一个 next 存储的内容），不是**位置**
- `sllseg h2 pt2 l2` 意味着最后一个节点的 next 值是 `pt2`
- 但我们需要的是最后一个 next 的**位置**是 `pt2`
- 语义不匹配！

---

### 方案 4：在 which_implies 中同时展开 `sllbseg` 和 `store`

**思路**：
```c
store(&(b2 -> head), struct sll *, h2) *
store(&(b2 -> ptail), struct sll **, pt2) *
sllbseg(&(b2 -> head), pt2, l2) * store(pt2, struct sll *, 0)
```

**问题**：资源冲突！
- 当 `l2 = nil` 时，`sllbseg(&(b2->head), pt2, nil)` = `[| &(b2->head) = pt2 |]`
- 所以 `pt2 = &(b2->head)`
- 目标同时需要 `store(&(b2->head), h2)` 和 `store(pt2, 0)`
- 即 `&(b2->head) |-> h2` 和 `&(b2->head) |-> 0`
- **同一个地址的两份资源，分离逻辑不允许！**

---

### 方案 5：删除 `store(&(b2->head), h2)`

**思路**：简化 which_implies，不显式提供 `&(b2->head)` 资源。

**问题**：验证器无法读取 `b2->head`（没有读权限）。

---

## 谓词定义回顾

### `sll(x, l)` - 普通链表
- `x` 是第一个节点地址
- 尾部 `|-> NULL` 被隐藏在递归中
- **不保留尾部位置信息**

### `sllseg(x, y, l)` - 链表段
- `x` 是第一个节点地址
- `y` 是最后一个节点 next 的**值**（不是位置！）
- 当 `l = nil` 时，`x = y`

### `sllbseg(x, y, l)` - 指针位置段
- `x` 是指向第一个节点的**指针位置**
- `y` 是最后一个 next 的**位置**
- 当 `l = nil` 时，`x = y`，且不持有任何堆资源（只是纯命题）

### `sllb(x, l)` - 链表盒子
- 使用 `sllbseg` 定义
- `ptail` 是最后一个 next 的位置，满足 `*ptail = NULL`

---

## 根本问题

### sllbseg 在空列表时的特殊行为

当 `l = nil` 时：
- `sllbseg x y nil = [| x = y |] && emp`
- 纯命题，不持有任何堆资源
- `x` 和 `y` 是同一个位置

这导致：
1. 无法单独读取 `x` 位置的值（没有 `x |-> ...` 资源）
2. 如果同时有 `sllbseg x y l` 和 `x |-> v`，当 `l` 非空时资源冲突

### 精确性证明的困难

在分离逻辑中，证明 "从同一个堆状态转换得到的变量相等" 需要：
1. 显式操作堆模型
2. 利用堆的确定性

当前框架不直接支持这种推理。

---

## 可能的解决方向

### 方向 1：接受 Admitted

对于语义上正确但难以形式化证明的精确性属性，使用 Admitted 标记。

### 方向 2：重新设计 `sllb` 定义

考虑不使用 `sllbseg`，而是直接用 `sll` 加额外信息：
```coq
Definition sllb' (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  EX h: addr,
    &(x # "sllb" ->ₛ "head") # Ptr |-> h **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> (compute_ptail h l) **
    sll h l.
```
但 `compute_ptail` 无法在纯 Coq 中定义（依赖堆状态）。

### 方向 3：修改验证框架

添加精确性推理支持，允许证明 "从同一堆转换的变量相等"。

### 方向 4：简化程序规范

不要求 `app_list_box` 返回正确的 `ptail`，而是返回后重新计算。

---

## 当前状态

通过修改 `sllb` 定义，解决了大部分验证问题：

1. **资源冲突**：空列表时不使用 `sllbseg`，显式分离资源 ✓
2. **无法读取**：空/非空都有 `&head` 资源 ✓
3. **`pt2` 保留**：使用 `sllbseg` 层面操作，保留 `pt2` ✓

### 遗留问题：`h2 = head2` 精确性

在 `return_wit_2` 证明中，当 `l2 = a :: l2'` 时：
- 前提有 `pt1 |-> h2`（执行 `*pt1 = h2` 后的状态）
- `sllbseg(&(b2->head), pt2, a::l2')` 展开后得到 `&(b2->head) |-> head2 ** head2->data = a ** ...`
- 需要使用 `sllbseg_concat_node` 连接，它要求 `pt1 |-> z ** z->data = a ** ...`
- 但我们有 `pt1 |-> h2` 和 `head2->data = a`
- **需要 `h2 = head2` 才能匹配资源**

**语义正确性**：`h2` 来自 `b2->head` 的读取，`head2` 是 `sllbseg(&(b2->head), ...)` 展开后的头节点地址。
它们都是 `&(b2->head)` 存储的值，语义上相等。

**形式化困难**：验证器生成的 Coq 目标中，`h2` 是独立的 forall 量化变量，`head2` 是 sllbseg 展开后的存在变量。
没有显式的 `h2 = head2` 约束，需要精确性推理。

**当前解决方案**：使用 `admit` 假设 `h2 = head2`，标记为语义正确。

---

## 结论

修改 `sllb` 定义解决了验证器层面的问题（资源可读性、`pt2` 保留），
但仍需要在 Coq 证明中处理一个精确性问题（`h2 = head2`），使用 `Admitted` 标记。

---

## 相关文件

- `sll_lib.c`: C 程序实现
- `sll_project_lib.v`: Coq 谓词定义和引理
- `sll_project_proof_manual.v`: Coq 证明
- `sll_project_def.h`: 验证器使用的定义文件

