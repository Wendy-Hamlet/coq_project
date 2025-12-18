# sllb 谓词及引理说明

本文档说明 `sll_project_lib.v` 中定义的 `sllb` 谓词及其相关引理。

## 1. 数据结构定义

### C 结构体

```c
struct sll {
    unsigned int data;  // 注意：unsigned int 对应 Coq 中的 UInt
    struct sll * next;
};

struct sllb {
    struct sll * head;
    struct sll ** ptail;
};
```

### Coq 谓词

#### sll (单链表)

```coq
Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
  | nil     => [| x = NULL |] && emp
  | a :: l0 => [| x <> NULL |] && 
               EX y: addr,
                 &(x # "sll" ->ₛ "data") # UInt |-> a **
                 &(x # "sll" ->ₛ "next") # Ptr |-> y **
                 sll y l0
  end.
```

#### sllbseg (链表段)

```coq
Fixpoint sllbseg (x y: addr) (l: list Z): Assertion :=
  match l with
  | nil     => [| x = y |] && emp
  | a :: l0 => EX z: addr,
                 [| z <> NULL |] &&
                 x # Ptr |-> z **
                 &(z # "sll" ->ₛ "data") # UInt |-> a **
                 sllbseg (&(z # "sll" ->ₛ "next")) y l0
  end.
```

#### sllb (链表盒子)

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  EX ptail_val: addr,
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
    ptail_val # Ptr |-> NULL.
```

**设计要点**：
- 使用 `sllbseg` 描述链表内容，显式持有 `*ptail = NULL` 的权限
- 空列表：`head = NULL`, `ptail = &head`
- 非空列表：`sllbseg` 从 `&head` 到 `ptail`，`*ptail = NULL`

## 2. 引理列表

### 展开类（从 sllb 推导信息）

| 引理 | 功能 |
|-----|-----|
| `sllb_zero` | 空 sllb：得到 `head=NULL, ptail=&head` |
| `sllb_not_zero` | 非空 sllb：暴露首节点数据 |
| `sllb_2_sllbseg` | 转换为 sllbseg 表示 |
| `sllb_2_sll` | 转换为 sll 表示 |

### 折叠类（构造 sllb）

| 引理 | 功能 |
|-----|-----|
| `sllb_len1` | 从空列表字段值构造 sllb |
| `sllbseg_2_sllb` | 从 sllbseg 结构构造 sllb |

### 转换类

| 引理 | 功能 |
|-----|-----|
| `sllbseg_0_sll'` | `sllbseg + *y=NULL` → `sll` |
| `sllbseg_sll` | `sllbseg + sll` 拼接 |
| `sll_2_sllbseg` | `sll` → `sllbseg + *pt=NULL` |
| `sll_2_sllb` | 辅助引理 |
