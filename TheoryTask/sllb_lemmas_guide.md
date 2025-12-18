# sllb 引理设计说明

本文档讲解 `sll_project_lib.v` 中新设计的 `sllb` 谓词及其相关引理。

## 1. sllb 谓词定义

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  EX ptail_val: addr,
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
    ptail_val # Ptr |-> NULL.
```

### 设计理念

`sllb` 表示一个 "list box" 结构，对应 C 代码中的：

```c
struct sllb {
    struct sll * head;
    struct sll ** ptail;
};
```

**关键设计**：
- 使用 `sllbseg` 而非 `sll` 来描述链表内容
- 显式包含 `*ptail = NULL` 的权限
- 这样设计使得 `app_list_box` 等函数的验证更加自然

### 语义解释

| 列表状态 | head | ptail | 内存布局 |
|---------|------|-------|---------|
| 空列表 `nil` | `NULL` | `&head` | `ptail_val = &head`，`*ptail = head = NULL` |
| 非空列表 `a::l` | 第一个节点 | 最后节点的 `&next` | `*ptail = NULL`（链表终止） |

## 2. 引理总览

### 2.1 展开类引理（从 sllb 推导信息）

| 引理 | 作用 |
|-----|-----|
| `sllb_zero` | 空 sllb 展开：得到 `head=NULL, ptail=&head` |
| `sllb_not_zero` | 非空 sllb 展开：暴露第一个节点的数据 |
| `sllb_2_sllbseg` | 转换为 sllbseg 表示（直接从定义） |
| `sllb_2_sll` | 转换为 sll 表示 |

### 2.2 折叠类引理（构造 sllb）

| 引理 | 作用 |
|-----|-----|
| `sllb_len1` | 从空列表的字段值构造 sllb |
| `sllbseg_2_sllb` | 从 sllbseg 结构构造 sllb |

### 2.3 转换类引理（谓词间转换）

| 引理 | 作用 |
|-----|-----|
| `sllbseg_0_sll'` | `sllbseg + *y=NULL` → `sll` |
| `sllbseg_sll` | `sllbseg + sll` 拼接 |
| `sllbseg_sll'` | `sllbseg + *y=0 + sll 0` 特殊情况 |

## 3. 引理详解

### 3.1 `sllb_zero`

```coq
Lemma sllb_zero: forall x,
  sllb x nil |--
  [| x <> NULL |] &&
  &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> &(x # "sllb" ->ₛ "head").
```

**含义**：空的 list box 满足：
- `box->head = NULL`
- `box->ptail = &(box->head)`（指向 head 字段本身）

**用途**：验证 `nil_list_box` 返回后的状态。

### 3.2 `sllb_not_zero`

```coq
Lemma sllb_not_zero: forall x a l,
  sllb x (a :: l) |--
  EX head_val ptail_val: addr,
    [| x <> NULL |] &&
    [| head_val <> NULL |] &&
    &(x # "sllb" ->ₛ "head") # Ptr |-> head_val **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    &(head_val # "sll" ->ₛ "data") # Int |-> a **
    sllbseg (&(head_val # "sll" ->ₛ "next")) ptail_val l **
    ptail_val # Ptr |-> NULL.
```

**含义**：非空 list box 可以展开为：
- `box->head` 指向第一个节点
- 第一个节点的 `data` 字段存储 `a`
- 剩余列表 `l` 由 `sllbseg` 表示
- `*ptail = NULL`

**用途**：验证需要访问第一个元素的操作，如 `cons_list_box`。

### 3.3 `sllb_2_sllbseg`

```coq
Lemma sllb_2_sllbseg: forall x l,
  sllb x l |--
  EX ptail_val: addr,
    [| x <> NULL |] &&
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
    ptail_val # Ptr |-> NULL.
```

**含义**：直接展开 `sllb` 定义。

**用途**：`app_list_box` 需要访问 `*ptail` 来连接两个链表。

### 3.4 `sllb_2_sll`

```coq
Lemma sllb_2_sll: forall x l,
  sllb x l |--
  EX head_val ptail_val: addr,
    [| x <> NULL |] &&
    &(x # "sllb" ->ₛ "head") # Ptr |-> head_val **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sll head_val l.
```

**含义**：将 `sllb` 转换为 `sll` 表示（隐藏 `*ptail` 权限）。

**用途**：当只需要读取/遍历链表而不需要修改 `*ptail` 时使用，如 `map_list_box`、`free_list_box`。

### 3.5 `sllbseg_2_sllb`

```coq
Lemma sllbseg_2_sllb: forall x ptail_val l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
  sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
  ptail_val # Ptr |-> NULL |--
  sllb x l.
```

**含义**：从 `sllbseg` 结构重新折叠为 `sllb`。

**注意**：不需要单独提供 `&head |-> head_val`，因为 `sllbseg` 已经包含了 `&head` 的权限。

**用途**：在修改操作完成后，重新构造 `sllb` 谓词。

## 4. 使用示例

### 示例 1：验证 `nil_list_box`

```coq
(* 目标：证明 sllb(box, nil) *)
(* 已知：box->head = NULL, box->ptail = &box->head *)
sep_apply sllb_len1.  (* 构造空 sllb *)
```

### 示例 2：验证 `app_list_box`

```coq
(* 需要访问 *ptail 来连接链表 *)
sep_apply sllb_2_sllbseg.  (* 展开为 sllbseg + *ptail=NULL *)
(* 现在可以写入 *(b1->ptail) = b2->head *)
```

### 示例 3：验证 `map_list_box`

```coq
(* 只需要遍历链表，不需要修改 *ptail *)
sep_apply sllb_2_sll.  (* 转换为 sll 表示 *)
(* 调用 map_list(box->head, x) *)
```

## 5. 命名规范

遵循课程 `sll_lib.v` 的命名风格：

| 模式 | 含义 | 示例 |
|-----|-----|-----|
| `xxx_zero` | 谓词在空/null 情况 | `sllb_zero` |
| `xxx_not_zero` | 谓词在非空情况 | `sllb_not_zero` |
| `xxx_len1` | 单元素/基础情况 | `sllb_len1` |
| `xxx_2_yyy` | 从 xxx 转换到 yyy | `sllb_2_sll` |
| `xxx_yyy` | xxx 与 yyy 的组合 | `sllbseg_sll` |
| `xxx'` | 变体版本 | `sllbseg_0_sll'` |

## 6. 与课程引理的对应关系

| 课程引理 (sll) | 本项目引理 (sllb) |
|--------------|------------------|
| `sll_zero` | `sllb_zero` |
| `sll_not_zero` | `sllb_not_zero` |
| `sllseg_len1` | `sllb_len1` |
| `sllbseg_2_sllseg` | `sllb_2_sllbseg` |
| `sllseg_0_sll` | `sllbseg_0_sll'` |
| `sllseg_sll` | `sllbseg_sll` |

