# 分离逻辑谓词与引理设计说明

本文档详细说明 `sll_project_lib.v` 中定义的分离逻辑谓词及其引理的设计思想。

## 1. 谓词定义

### 1.1 基础谓词

#### `sll`：单链表谓词

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

**设计要点**：
- 空链表：`x = NULL`
- 非空链表：`x` 指向首节点，递归定义后继节点
- 标准的递归单链表表示

#### `sllseg`：单链表段谓词

```coq
Fixpoint sllseg (x y: addr) (l: list Z): Assertion :=
  match l with
  | nil     => [| x = y |] && emp
  | a :: l0 => [| x <> NULL |] && 
               EX z: addr,
                 &(x # "sll" ->ₛ "data") # UInt |-> a **
                 &(x # "sll" ->ₛ "next") # Ptr |-> z **
                 sllseg z y l0
  end.
```

**设计要点**：
- 描述从节点 `x` 到节点 `y` 的链表段
- 空段：`x = y`
- 非空段：从 `x` 开始，递归到 `y`
- 用于描述链表的一部分

### 1.2 链表盒子专用谓词

#### `sllbseg`：链表盒子段谓词

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

**与 `sllseg` 的关键区别**：
- `x` 不是节点地址，而是**指针的地址**（`x` 存储指向节点的指针）
- `x # Ptr |-> z`：`x` 位置存储指针 `z`
- `y` 是尾部指针位置（指向下一个节点应该连接的位置）
- 递归参数是 `&(z # "sll" ->ₛ "next")`，即下一个指针的地址

**用途**：精确描述 `&head` 到 `ptail` 之间的链表结构

#### `sllb`：链表盒子谓词

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  match l with
  | nil =>
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.
```

**设计要点**：
- **分情况定义**：空/非空链表的 `ptail` 语义不同
- **空链表**：`head = NULL`，`ptail = &head`（指向 `head` 字段本身）
- **非空链表**：`ptail` 指向最后一个节点的 `next` 字段，且 `*ptail = NULL`
- **精确性**：持有 `ptail # Ptr |-> NULL` 的所有权，支持直接修改尾部

### 1.3 辅助谓词

#### `sll_pt`：带尾指针的单链表

```coq
Definition sll_pt (h: addr) (pt: addr) (l: list Z): Assertion :=
  match l with
  | nil => [| h = NULL |] && emp
  | a :: l0 =>
      [| h <> NULL |] &&
      &(h # "sll" ->ₛ "data") # UInt |-> a **
      sllbseg (&(h # "sll" ->ₛ "next")) pt l0 **
      pt # Ptr |-> NULL
  end.
```

**用途**：在 `app_list_box` 中使用，显式暴露链表的尾指针位置 `pt`

#### `sllb_sll`：基于 `sll` 的链表盒子视图

```coq
Definition sllb_sll (x: addr) (l: list Z): Assertion :=
  [| x <> 0 |] &&
  EX h: addr,
    &(x # "sllb" ->ₛ "head") # Ptr |-> h **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> 0 **
    sll h l.
```

**设计要点**：
- 将 `ptail` 设为 0（无意义值），不跟踪尾指针精确位置
- 用于**只读操作**（`map_list_box`、`sllb2array`）
- 避免在只读遍历时维护 `ptail` 的精度约束
- 简化证明，允许调用底层的 `sll` 相关函数

#### `map_mult`：列表映射函数

```coq
Definition map_mult (x: Z) (l: list Z): list Z :=
  List.map (fun a => unsigned_last_nbits (x * a) 32) l.
```

**用途**：指定 `map_list_box` 的功能语义（将每个元素乘以 `x`，结果模 $2^{32}$）

## 2. 引理分类与设计

### 2.1 `sll` 引理（Part 2）

| 引理 | 功能 | 用途 |
|------|------|------|
| `sll_zero` | `x = NULL` → `l = nil` | 判断空链表 |
| `sll_not_zero` | `x <> NULL` → 展开首节点 | 访问非空链表的首元素 |
| `sll_not_zero'` | `x <> NULL` → `l <> nil` | 证明非空性 |
| `sll_not_null_length` | `x <> NULL` → `Zlength l >= 1` | 长度约束 |

### 2.2 `sllseg` 引理（Part 3）

| 引理 | 功能 | 用途 |
|------|------|------|
| `sllseg_len1` | 构造长度为 1 的段 | 单节点段的折叠 |
| `sllseg_sllseg` | 连接两个段：`sllseg x y l1 ** sllseg y z l2 \|-- sllseg x z (l1 ++ l2)` | 段拼接 |
| `sllseg_sll` | 段与链表拼接：`sllseg x y l1 ** sll y l2 \|-- sll x (l1 ++ l2)` | 段转完整链表 |
| `sllseg_0_sll` | `sllseg x 0 l \|-- sll x l` | 以 NULL 结尾的段即完整链表 |

### 2.3 `sllbseg` 引理（Part 4）

| 引理 | 功能 | 用途 |
|------|------|------|
| `sllbseg_len1` | 构造长度为 1 的盒子段 | 单节点盒子段的折叠 |
| `sllbseg_sllbseg` | 连接两个盒子段 | 盒子段拼接 |
| `sllbseg_2_sllseg` | `sllbseg x y l ** y # Ptr \|-> z \|-- sllseg ... l` | 盒子段转普通段 |
| `sllbseg_0_sll'` | `sllbseg x y l ** y # Ptr \|-> NULL \|-- sll ... l` | 盒子段转完整链表 |
| `sllbseg_sll'` | 盒子段与空链表拼接 | 特殊情况 |
| `sllbseg_sll` | `sllbseg x y l1 ** y # Ptr \|-> z ** sll z l2 \|-- sll ... (l1 ++ l2)` | 盒子段与链表拼接 |
| `sllbseg_0_sll_pt` | `sllbseg x pt l ** pt # Ptr \|-> NULL \|-- sll_pt ... l` | 盒子段转带尾指针的链表 |
| **`sllbseg_append_sllbseg`** | **连接两个盒子段形成新段** | **`app_list_box` 的核心引理** |

#### 核心引理详解：`sllbseg_append_sllbseg`

```coq
Lemma sllbseg_append_sllbseg: forall x pt1 l1 h2 pt2 a l2,
  h2 <> NULL ->
  sllbseg x pt1 l1 ** 
  pt1 # Ptr |-> h2 ** 
  &(h2 # "sll" ->ₛ "data") # UInt |-> a **
  sllbseg (&(h2 # "sll" ->ₛ "next")) pt2 l2 **
  pt2 # Ptr |-> NULL |--
  sllbseg x pt2 (l1 ++ a :: l2) ** pt2 # Ptr |-> NULL.
```

**语义**：
- 前提：段 `l1` 从 `x` 到 `pt1`，`pt1` 指向节点 `h2`，从 `h2` 开始是段 `l2`
- 结论：可以形成从 `x` 到 `pt2` 的完整段 `l1 ++ a :: l2`

**证明方法**：对 `l1` 归纳
- **Base case** (`l1 = nil`)：`x = pt1`，直接构造新段
- **Inductive case**：展开 `l1` 的首节点，对尾部应用归纳假设

**用途**：形式化 `*(b1->ptail) = b2->head` 这一双重指针操作的语义

### 2.4 `sllb` 引理（Part 5）

#### 展开引理（Unfold）

| 引理 | 功能 | 返回形式 | 特点 |
|------|------|---------|------|
| `sllb_2_sllbseg` | 展开为盒子段形式 | `sllbseg + ptail` | **保留精确尾指针** |
| `sllb_2_sll` | 展开为链表形式 | `sll + head + ptail` | 丢失尾指针精度 |
| `sllb_2_sll_pt` | 展开为带尾指针链表 | `sll_pt + head + ptail` | **保留尾指针位置** |

**使用场景**：
- `sllb_2_sllbseg`：用于需要修改尾指针的函数（`app_list_box`、`cons_list_box`）
- `sllb_2_sll`：用于策略 32（自动展开）
- `sllb_2_sll_pt`：用于 `app_list_box` 的第二个参数（需要知道 `b2` 的尾指针）

#### 折叠引理（Fold）

| 引理 | 功能 | 用途 |
|------|------|------|
| `sllbseg_2_sllb` | 从盒子段折叠回 `sllb` | 在修改后重建 `sllb` 不变式 |

**前提条件**：
- `x <> NULL`（盒子指针非空）
- 持有 `sllbseg (&(x # "sllb" ->ₛ "head")) pt l` 和 `pt # Ptr |-> NULL`