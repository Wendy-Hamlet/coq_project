# sllb2array 验证问题分析与尝试记录

## 问题背景

`sllb2array` 函数将 `sllb`（链表盒子）的内容复制到数组，其逻辑很简单：
```c
unsigned int sllb2array(struct sllb *box, unsigned int **out_array)
{
    return sll2array(box->head, out_array);
}
```

验证规约：
```c
/*@ With l
    Require sllb(box, l) && Zlength(l) <= 2147483647 && undef_data_at(out_array, unsigned int *)
    Ensure exists arr_ret, sllb(box@pre, l) && store(out_array@pre, unsigned int *, arr_ret) &&
           UIntArray::full_shape(arr_ret, Zlength(l))
*/
```

## 核心问题

### 验证条件 `sllb2array_return_wit_1`

```coq
Definition sllb2array_return_wit_1 := 
forall (out_array_pre box_pre l pt h arr_ret_2: Z),
  [| box_pre <> 0 |] && [| Zlength l <= INT_MAX |] &&
  sll h l **
  out_array_pre # Ptr |-> arr_ret_2 **
  UIntArray.full_shape arr_ret_2 (Zlength l) **
  &(box_pre # "sllb" ->ₛ "head") # Ptr |-> h **
  &(box_pre # "sllb" ->ₛ "ptail") # Ptr |-> pt
|--
  EX arr_ret,
    sllb box_pre l **
    out_array_pre # Ptr |-> arr_ret **
    UIntArray.full_shape arr_ret (Zlength l).
```

### 语义解读

**前提条件（左侧）**：
- `sll h l` — 从头指针 `h` 开始的单链表，内容为 `l`
- `&(box_pre->head) |-> h` — box 的 head 字段存储 `h`
- `&(box_pre->ptail) |-> pt` — box 的 ptail 字段存储 `pt`

**后置条件（右侧）**：
- `sllb box_pre l` — 需要重建完整的 `sllb` 结构

### 问题分析

回顾 `sllb` 的定义：

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  match l with
  | nil =>
      (* 空链表：显式提供 head 和 ptail 资源 *)
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      (* 非空链表 *)
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.
```

**问题 1：空链表情况 (l = nil)**

当 `l = nil` 时，`sllb box_pre nil` 要求：
- `&(box_pre->head) |-> NULL`
- `&(box_pre->ptail) |-> &(box_pre->head)`（ptail 必须指向 head 字段的地址）

但前提条件只给了：
- `&(box_pre->head) |-> h`
- `&(box_pre->ptail) |-> pt`

**问题**：需要证明 `h = NULL` 且 `pt = &(box_pre->head)`，但 `pt` 是自由变量，没有约束！

**问题 2：非空链表情况 (l = a :: l0)**

当非空时，`sllb box_pre l` 要求：
- `EX ptail_val, &(box_pre->ptail) |-> ptail_val ** sllbseg (&(box_pre->head)) ptail_val l ** ptail_val |-> NULL`

但前提条件给的是：
- `sll h l` — 普通的 `sll`，不是 `sllbseg`
- `&(box_pre->ptail) |-> pt` — `pt` 是什么？

**问题**：
- 需要把 `sll h l` 转换成 `sllbseg (&(box_pre->head)) ptail_val l`
- 需要证明 `pt` 就是链表尾部的指针位置
- 需要证明 `ptail_val |-> NULL`
- 但 `pt` 没有任何约束说明它与链表尾部的关系！

---

## 根本原因

验证条件缺少关键的不变量信息：

1. **`pt` 的语义不明确**：`pt` 来自 `which_implies_wit_1` 展开 `sllb` 时产生的，应该满足某些性质，但这些性质丢失了。

2. **信息丢失于 which_implies**：当把 `sllb` 展开成 `&(box->head) |-> h ** &(box->ptail) |-> pt ** sll h l` 时，关于 `pt` 与 `sll h l` 尾部关系的信息丢失了。

3. **`sll` 不携带尾指针信息**：`sll h l` 只知道从 `h` 开始有个链表内容为 `l`，但不知道尾指针在哪里。

---

## 尝试的方案及失败记录

### 方案 1：在 which implies 中使用 sll_pt

**思路**：让 `which_implies` 输出 `sll_pt h pt l` 而不是 `sll h l`

```c
/*@ sllb(box, l)
    which implies
    exists h pt,
        box != 0 &&
        store(&(box -> head), struct sll *, h) *
        store(&(box -> ptail), struct sll **, pt) *
        sll_pt(h, pt, l)
*/
```

**结果**：❌ 失败

**错误**：
```
fatal error: Cannot derive the precondition of function sll2array for spec (null)
```

**原因**：`sll2array` 期望 `sll(head, l)`，不是 `sll_pt(h, pt, l)`

---

### 方案 2：嵌套 which implies 转换

**思路**：在调用 `sll2array` 前，用另一个 `which implies` 把 `sll_pt` 转成 `sll`

```c
/*@ sllb(box, l)
    which implies
    exists h pt,
        box != 0 &&
        store(&(box -> head), struct sll *, h) *
        store(&(box -> ptail), struct sll **, pt) *
        sll_pt(h, pt, l)
*/
/*@ sll_pt(box -> head, pt, l)
    which implies
    sll(box -> head, l)
*/
return sll2array(box->head, out_array);
```

**结果**：❌ 失败

**错误**：
```
fatal error: Use of undeclared identifier `pt'
```

**原因**：`pt` 是第一个 `which implies` 的存在量化变量，在第二个 `which implies` 的作用域外

---

### 方案 3：修改 sll2array 规约使用 sll_pt

**思路**：让 `sll2array` 接受 `sll_pt` 而不是 `sll`

```c
unsigned int sll2array(struct sll *head, unsigned int **out_array)
/*@ With l pt
    Require sll_pt(head, pt, l) && Zlength(l) <= 2147483647 && ...
    Ensure sll_pt(head@pre, pt, l) && ...
*/
```

**结果**：❌ 失败

**错误**：
```
fatal error: Partial Solve Invariant Error
```

**原因**：循环不变式也需要修改

---

### 方案 4：同时修改 sll_length 和 sll2array

**思路**：让整个调用链都使用 `sll_pt`

```c
unsigned int sll_length(struct sll *head)
/*@ With l pt
    Require sll_pt(head, pt, l) && ...
*/
{
    /*@ Inv sllseg(head@pre, head, l1) * sll_pt(head, pt, l2) */
    while (head) { ... }
}
```

**结果**：❌ 失败

**问题分析**：

`sll_pt` 的定义：
```coq
Definition sll_pt (h: addr) (pt: addr) (l: list Z): Assertion :=
  match l with
  | nil => [| h = NULL |] && emp
  | a :: l0 => [| h <> NULL |] && &(h->data) |-> a ** sllbseg (&(h->next)) pt l0 ** pt |-> NULL
  end.
```

**核心问题**：当 `l = nil` 时，`sll_pt nil` 只是 `[| h = NULL |] && emp`，不包含 `pt |-> NULL`！

在循环中：
1. 初始：`sll_pt head pt (a::l0)` 包含 `pt |-> NULL`
2. 迭代：每次消耗一个节点
3. 结束：`sll_pt head pt nil = [| head = NULL |] && emp`

**资源丢失**：`pt |-> NULL` 在循环结束时消失了！

---

### 方案 5：修改 sll_pt 定义（nil 时包含 pt |-> NULL）

**思路**：
```coq
Definition sll_pt (h: addr) (pt: addr) (l: list Z): Assertion :=
  match l with
  | nil => [| h = NULL |] && pt # Ptr |-> NULL  (* 添加资源 *)
  | a :: l0 => ...
  end.
```

**结果**：❌ 失败

**问题**：
1. 会破坏 `app_list_box` 的证明
2. `sllb` 空链表时 `pt = &(box->head)`，但 `&(box->head) |-> NULL` 已经在 `sllb` 定义中
3. 资源重复/冲突

---

### 方案 6：使用 sllbseg 代替 sll

**思路**：在 `which implies` 中保留 `pt` 的精确关系

```c
/*@ sllb(box, l)
    which implies
    exists pt,
        box != 0 &&
        store(&(box -> ptail), struct sll **, pt) *
        sllbseg(&(box -> head), pt, l) *
        store(pt, struct sll *, 0)
*/
/*@ sllbseg(...) * store(pt, 0)
    which implies
    sll(box -> head, l)
*/
return sll2array(box->head, out_array);
```

**结果**：⚠️ 部分成功，但有新问题

**问题**：第二个 `which implies` 丢失 `pt` 信息。调用 `sll2array` 后返回 `sll`，无法恢复 `sllbseg + pt`。

---

### 方案 7：完全使用 sllbseg 贯穿调用链

**思路**：让 `sll_length` 和 `sll2array` 使用 `sllbseg + store(pt, 0)` 而非 `sll`

```c
unsigned int sll_length(struct sll *head)
/*@ With l pt
    Require sllbseg(&head, pt, l) * store(pt, struct sll *, 0) && ...
*/
```

**结果**：❌ 失败

**原因**：`&head` 是局部变量的地址，不能用于 `sllbseg`。`sllbseg` 的第一个参数应该是堆上的位置，不是栈上的。

---

### 方案 8（当前）：回到 sll，接受限制

**当前状态**：
```c
/*@ sllb(box, l)
    which implies
    exists h pt,
        box != 0 &&
        store(&(box -> head), struct sll *, h) *
        store(&(box -> ptail), struct sll **, pt) *
        sll(h, l)
*/
return sll2array(box->head, out_array);
```

**验证条件**：需要从 `sll h l + stores` 恢复 `sllb box l`

**待解决**：需要辅助引理证明转换可行

---

## 与 app_list_box 对比

| 特性 | app_list_box | sllb2array |
|------|--------------|------------|
| 问题类型 | `pt2 = pt_final` 精确性 | `pt` 与链表尾部关系 |
| which implies | ✓ 使用 sll_pt 解决 | ✗ sll_pt 不适用于循环 |
| 资源保留 | sllbseg 保留 pt | sll 丢失 pt |
| 函数调用 | 无外部调用 | 调用 sll2array |
| 循环 | 无 | 有（在 sll2array 中） |

### 关键差异

`app_list_box` 不涉及循环，`sll_pt` 可以直接在入口展开、出口重建。

`sllb2array` 调用 `sll2array`，后者有循环：
- 循环需要不变式
- `sll_pt` 在循环中会丢失 `pt |-> NULL` 资源
- `sll` 适合循环但丢失 `pt` 信息

---

## 问题的本质

### 谓词设计的权衡

| 谓词 | 优点 | 缺点 |
|------|------|------|
| `sll(h, l)` | 适合循环不变式 | 不追踪尾指针 |
| `sll_pt(h, pt, l)` | 追踪尾指针 | 空列表不持有资源，不适合循环 |
| `sllbseg(x, y, l)` | 精确追踪位置 | 空列表是纯命题，第一个参数必须是堆位置 |

### 信息流分析

```
sllb(box, l)
    ↓ which implies
store(&box->head, h) * store(&box->ptail, pt) * sll(h, l)
    ↓ 调用 sll2array
sll(h, l) ← 进入 sll2array
    ↓ 循环
sll(h, l) ← 返回
    ↓ 需要重建
sllb(box, l)  ← 需要 pt 与 l 的关系！
```

**问题**：`pt` 的语义信息在"进入 sll2array"时丢失，无法在"重建"时恢复。

---

## 可能的解决方向

### 方向 1：精确性公理

添加公理：如果 `pt` 来自 `sllb` 展开，则 `pt` 是链表的真正尾指针位置。

```coq
Axiom sllb_pt_is_tail: forall box l h pt,
  sllb box l |-- 
    &(box->head) |-> h ** &(box->ptail) |-> pt ** sll h l ** [| is_tail_ptr pt h l |].
```

**缺点**：需要定义 `is_tail_ptr`，依赖堆状态。

### 方向 2：重新设计 sllb

参考 `sll_queue` 的设计：
- 使用哨兵节点
- `ptail` 存储节点地址而非位置
- 空队列也有哨兵节点资源

### 方向 3：接受 Admitted

对语义正确但难以形式化的等式使用 Admitted。

### 方向 4：直接在 sllb2array 中实现逻辑

不调用 `sll2array`，直接实现遍历逻辑，使用 `sllbseg` 维护不变式。

---

## 经验教训

1. **循环不变式的选择**：`sll` 适合循环，因为空列表时 `sll NULL nil = emp`，不产生额外资源。

2. **尾指针追踪的代价**：追踪 `pt` 需要额外资源 `pt |-> NULL`，但这个资源在空列表时成为负担。

3. **谓词与函数签名的匹配**：修改内层函数的规约会导致连锁反应，需要仔细评估影响范围。

4. **which implies 的限制**：存在量化变量的作用域只在单个 `which implies` 内，不能跨越多个。

5. **参考成功案例**：`sll_queue` 使用哨兵设计避免了类似问题，值得学习。

---

## 当前状态

- **C 验证**：✓ 通过
- **Coq 证明**：
  - `sllb2array_which_implies_wit_1`：✅ 已完成（使用 `sllb_2_sll` 引理）
  - `sllb2array_return_wit_1`：❌ Admitted（精确性问题）

### sllb2array_return_wit_1 的精确性问题

验证条件：
```coq
sll h l ** &(box->head) |-> h ** &(box->ptail) |-> pt
|--
sllb box l
```

问题分析：
1. 使用 `sll_2_sllbseg` 将 `sll h l` 转换为 `sllbseg(&head, pt_new, l) ** pt_new |-> NULL`
2. `sllb` 的定义需要 `&(box->ptail) |-> pt_new`
3. 我们只有 `&(box->ptail) |-> pt`
4. **无法证明 `pt = pt_new`**

具体情况：
- **nil 情况**：`sllbseg nil` 蕴含 `pt_new = &(box->head)`，需要 `pt = &(box->head)`
- **cons 情况**：`sllbseg (a::l)` 产生某个 `pt_new`，需要 `pt = pt_new`

这与 `app_list_box` 的问题完全相同：`pt` 是 `which implies` 展开时的自由变量，
其与链表尾部的关系在调用 `sll2array` 后丢失。

---

## 方案8：使用 `||` 分情况的循环不变量

### 核心问题再分析

**`sll_pt` 的定义**：
```coq
Definition sll_pt (h pt: addr) (l: list Z): Assertion :=
  match l with
  | nil => [| h = NULL |] && emp
  | a :: l0 => [| h <> NULL |] &&
               &(h # "sll" ->ₛ "data") # UInt |-> a **
               sllbseg (&(h # "sll" ->ₛ "next")) pt l0 **
               pt # Ptr |-> NULL
  end.
```

**精确性问题的本质**：
1. `sll_pt nil` = `h = NULL && emp`（不包含 `pt |-> NULL`！）
2. `sll_pt (a::l)` 包含 `pt |-> NULL`
3. 循环遍历时，当 `l2` 从非空变成空时，`pt |-> NULL` 资源消失
4. 需要重建 `sll_pt l` 时，无法恢复 `pt |-> NULL`

**`sll` 方案失败的原因**：
从 `sll h l` 使用 `sll_2_sllbseg` 转换得到 `sllbseg ** pt_new |-> NULL`，
但 `pt_new` 是新产生的存在量化变量，不等于原来的 `pt`。
所以 `&ptail |-> pt` 无法变成 `&ptail |-> pt_new`。

### 解决方案：使用 `||` 分三种情况

关键洞察：我们需要在循环不变量中**始终保持 `pt` 信息**。

**三种情况**：
1. `l2 != nil`：使用 `sllseg * sll_pt`，`pt |-> NULL` 在 `sll_pt` 内部
2. `l2 == nil && l != nil`：遍历完成，展开为 `sllbseg(&head@pre->next, pt, tail(l)) * &head@pre->data |-> first(l) * pt |-> 0`
3. `l == nil`：空列表特殊情况，`head@pre == 0 && head == 0`

**循环不变量**：
```c
/*@ Inv exists l1 l2,
        l == app(l1, l2) &&
        len == Zlength(l1) &&
        (
          (l2 != nil && sllseg(head@pre, head, l1) * sll_pt(head, pt, l2)) ||
          (l2 == nil && l != nil && head == 0 &&
            &(head@pre -> data) |-> Znth(0, l, 0) *
            sllbseg(&(head@pre -> next), pt, tail(l)) *
            pt |-> 0) ||
          (l == nil && head@pre == 0 && head == 0)
        )
*/
```

**为什么这个方案有效**：
- `l2 != nil` 时：`sll_pt l2` 内部包含 `pt |-> NULL`，资源完整
- `l2 == nil && l != nil` 时：显式保留 `pt |-> NULL`，并用 `sllbseg` 跟踪 `pt` 位置
- `l == nil` 时：没有资源需要追踪

**循环结束后的重建**：
- 如果 `l != nil`：有 `sllbseg + pt |-> NULL`，可以直接重建 `sll_pt l`
- 如果 `l == nil`：`sll_pt nil = emp`，直接满足

---

## 相关文件

- `QCP_examples/sll_lib.c`: C 程序实现
- `SeparationLogic/examples/sll_project_lib.v`: Coq 谓词定义
- `SeparationLogic/examples/sll_project_goal.v`: 生成的验证条件
- `SeparationLogic/examples/sll_project_proof_manual.v`: 手动证明
- `app_list_box_verification_notes.md`: 相关问题的成功解决案例

---

## 时间线

| 阶段 | 事件 |
|------|------|
| 初始 | 队友发现 `sllb2array_return_wit_1` 无法证明 |
| 分析 | 确定问题根源：`pt` 与 `sll` 尾部关系丢失 |
| 方案1 | 尝试 `sll_pt` → 失败（sll2array 不接受） |
| 方案2 | 嵌套 which implies → 失败（pt 作用域问题） |
| 方案3-4 | 修改 sll2array/sll_length → 失败（循环资源丢失） |
| 方案5 | 修改 sll_pt 定义 → 失败（破坏其他证明） |
| 方案6-7 | 使用 sllbseg → 失败（局部变量地址问题） |
| 方案8 | **使用 `\|\|` 分情况的循环不变量** → 尝试中 |

