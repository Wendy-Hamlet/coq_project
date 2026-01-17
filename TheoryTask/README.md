# TheoryTask - 链表数据结构的 Coq 形式化验证

本任务对基于双重指针实现的链表数据结构（sllb）进行形式化验证，使用 Coq 和分离逻辑证明 C 程序的正确性。

## 1. 核心数据结构

### 1.1 基础链表节点（`sll`）

```c
struct sll {
    unsigned int data;
    struct sll *next;
};
```

标准单向链表节点，包含数据字段和指向下一个节点的指针。

### 1.2 List Box 结构（`sllb`）

```c
struct sllb {
    struct sll *head;     // 链表头指针
    struct sll **ptail;   // 指向尾部的双重指针
};
```

**设计思想**：`ptail` 是指向"下一个节点应该插入位置"的双重指针：
- **空链表**：`ptail` 指向 `&head`，写入 `*ptail` 直接更新头指针
- **非空链表**：`ptail` 指向最后一个节点的 `&next` 字段，写入 `*ptail` 将新节点链接到尾部

这种设计支持 **常数时间的尾部操作**，例如链表合并。

## 2. 分离逻辑谓词

### 2.1 `sllb` 谓词（精确版本）

定义在 `sll_project_lib.v` 中，用于需要修改链表结构的操作：

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  match l with
  | nil =>
      (* 空链表：ptail 指向 head 字段本身 *)
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      (* 非空链表：ptail 指向最后一个节点的 next 字段 *)
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.
```

**关键特性**：
- 精确跟踪 `ptail` 的指向位置
- 用于 `app_list_box`（链表合并）、`cons_list_box`（头部插入）等修改操作
- 区分空/非空情况以维护尾指针不变量

### 2.2 `sllb_sll` 谓词（宽松版本）

定义在 `sll_project_lib.v` 第60行，用于只读或不改变结构的操作：

```coq
Definition sllb_sll (x: addr) (l: list Z): Assertion :=
  [| x <> 0 |] &&
  EX h: addr,
    &(x # "sllb" ->ₛ "head") # Ptr |-> h **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> 0 **
    sll h l.
```

**用途**：
- 只读遍历（`sllb2array`、`map_list_box`）
- 释放操作（`free_list_box`）
- 避免尾指针精度问题，简化验证

### 2.3 辅助谓词

- **`sllbseg x y l`**：从地址 `x` 开始、到地址 `y`（指针位置）结束的链表段
- **`sll_pt h pt l`**：标准链表 `sll h l` 的扩展，额外暴露尾指针地址 `pt`

### 2.4 谓词组合策略与设计原理

本项目的验证采用了两套不同的谓词组合方案。选择哪套方案取决于函数是否需要在返回后继续进行链表连接操作。

对于需要连接功能的函数（如 `app_list_box` 和 `cons_list_box`），我们使用 `sll_pt` 和 `sllbseg` 来精确跟踪尾指针 `ptail` 的具体值。这种方式要求通过 `which implies` 将 `pt` 显式读取到 C 变量中，并避免调用会丢失 `pt` 信息的子函数。虽然验证更复杂，但能够保证函数返回时精确重建 `sllb` 谓词，从而支持后续的链表操作。

另一方面，对于只读遍历、转换或释放操作（如 `map_list_box`、`sllb2array`、`free_list_box`），我们使用 `sll` 和 `sllb_sll` 组合。这种方式主动放弃尾指针跟踪，将 `ptail` 字段设为 0。这样做避免了精确性问题——当内部需要调用带循环的 `sll` 函数（如 `sll2array`）时，如果保持 `sllbseg` 会导致 `sll` 遍历丢失 `pt` 与原始值的关联。使用 `sllb_sll` 从一开始就放弃 `pt` 跟踪，使谓词转换链路清晰匹配。代价是无法进行后续连接，但对于转数组或释放这样的终结性操作，这是可接受的设计选择。

详细的精确性问题分析参见 [precision_problem_analysis.md](precision_problem_analysis.md)。

---

## 3. 函数验证

本项目验证了12个函数，分为以下两类：

### 3.1 辅助函数（6个）

标准单向链表（`sll`）的基础操作，为关键函数提供支撑。

#### 3.1.1 `cons_list` - 链表头部插入

```c
struct sll *cons_list(unsigned int data, struct sll *next)
/*@ With l pt
    Require sll_pt(next, pt, l)
    Ensure exists pt_new,
           sll_pt(__return, pt_new, cons(data, l)) &&
           (l == nil && pt_new == &(__return -> next) || l != nil && pt_new == pt)
*/
```

**功能**：创建新节点，插入到链表头部。

**规约说明**：
- 使用 `sll_pt` 谓词暴露尾指针 `pt`
- 返回值保证：新链表的尾指针根据原链表是否为空而不同
  - 原链表为空：新尾指针指向新节点的 `&next`
  - 原链表非空：尾指针保持不变

#### 3.1.2 `free_list` - 释放整个链表

```c
void free_list(struct sll *head)
/*@ With l
    Require sll(head, l)
    Ensure emp
*/
{
  /*@ Inv exists l_rest, sll(head, l_rest) */
  while (head) {
    struct sll *tmp = head;
    head = head->next;
    free_list_node(tmp);
  }
}
```

**功能**：遍历链表并释放所有节点。

**循环不变量**：`sll(head, l_rest)` 表示剩余未释放的链表段。

#### 3.1.3 `map_list` - 链表元素映射

```c
void map_list(struct sll *head, unsigned int x)
/*@ With l
    Require sll(head, l)
    Ensure sll(head, map_mult(x, l))
*/
{
  /*@ Inv exists l1 l2, l == app(l1, l2) &&
          sllseg(head@pre, p, map_mult(x@pre, l1)) * sll(p, l2) &&
          head == head@pre && x == x@pre
  */
  for (p = head; p != (struct sll *)0; p = p->next) {
    p->data = x * p->data;
  }
}
```

**功能**：将链表中每个元素乘以 `x`（模 2^32）。

**循环不变量**：
- 链表分为已处理段 `sllseg(..., l1)` 和未处理段 `sll(..., l2)`
- 已处理段的数据已完成映射操作

**逻辑定义**（`sll_project_lib.v`）：
```coq
Definition map_mult (x: Z) (l: list Z): list Z :=
  List.map (fun a => unsigned_last_nbits (x * a) 32) l.
```

#### 3.1.4 `sll_length` - 计算链表长度

```c
unsigned int sll_length(struct sll *head)
/*@ With l
    Require sll(head, l) && Zlength(l) <= 2147483647
    Ensure __return == Zlength(l) && sll(head@pre, l)
*/
{
  unsigned int len = 0;
  /*@ Inv exists l1 l2,
          l == app(l1, l2) &&
          len == Zlength(l1) &&
          sllseg(head@pre, head, l1) * sll(head, l2)
  */
  while (head) {
    ++len;
    head = head->next;
  }
  return len;
}
```

**功能**：统计链表节点数量，不修改链表结构。

**关键性质**：后置条件保证原链表 `sll(head@pre, l)` 保持不变（只读操作）。

#### 3.1.5 `sll2array` - 链表转数组

```c
unsigned int sll2array(struct sll *head, unsigned int **out_array)
/*@ With l
    Require sll(head, l) && Zlength(l) <= 2147483647 && 
            undef_data_at(out_array, unsigned int *)
    Ensure exists arr_ret,
           sll(head@pre, l) &&
           store(out_array@pre, unsigned int *, arr_ret) &&
           UIntArray::full_shape(arr_ret, Zlength(l))
*/
{
  unsigned int len = sll_length(head);
  unsigned int *arr = new_uint_array(len);
  unsigned int i = 0;
  struct sll *p = head;
  
  /*@ Inv exists l1 l2,
          l == app(l1, l2) &&
          i == Zlength(l1) &&
          sllseg(head@pre, p, l1) * sll(p, l2) *
          UIntArray::ceil_shape(arr, 0, i) *      // 已填充 [0, i)
          UIntArray::undef_ceil(arr, i, len)      // 未初始化 [i, len)
  */
  while (p) {
    arr[i] = p->data;
    i = i + 1;
    p = p->next;
  }
  *out_array = arr;
  return len;
}
```

**功能**：分配数组并复制链表元素。

**循环不变量设计**：
- 数组分为已填充部分 `ceil_shape(arr, 0, i)` 和未定义部分 `undef_ceil(arr, i, len)`
- 链表分为已遍历段 `sllseg(..., l1)` 和剩余段 `sll(..., l2)`

**数组验证策略**：
- **Strategy 72**：证明可安全写入 `arr[i]`，分割未定义段
- **Strategy 92**：循环结束时，`ceil_shape(arr, 0, len)` 等价于 `full_shape(arr, len)`

#### 3.1.6 `nil_list` - 创建空链表

```c
struct sll *nil_list()
/*@ Require emp
    Ensure sll(__return, nil)
*/
{
  return (struct sll *)0;
}
```

**功能**：返回空指针表示空链表。

**规约**：从空资源生成 `sll(NULL, nil)`。

---

### 3.2 关键函数（6个）

List Box（`sllb`）结构的核心操作，实现高效尾部访问。

#### 3.2.1 `nil_list_box` - 创建空 List Box

```c
struct sllb *nil_list_box()
/*@ Require emp
    Ensure __return != 0 &&
           store(&(__return -> head), struct sll *, 0) *
           store(&(__return -> ptail), struct sll **, &(__return -> head))
*/
{
  struct sllb *box = new_sllb();
  box->head = nil_list();
  box->ptail = &box->head;
  return box;
}
```

**功能**：初始化一个空 List Box。

**关键初始化**：
- `box->head = NULL`
- `box->ptail = &box->head`（空链表不变量：尾指针指向头指针本身）

**验证特性**：
- 后置条件直接描述物理内存状态（而非折叠的 `sllb` 谓词）
- 全自动验证，无需手动证明

#### 3.2.2 `cons_list_box` - List Box 头部插入

```c
struct sllb *cons_list_box(unsigned int data, struct sllb *box)
/*@ With l pt
    Require box != 0 &&
            (pt == &(box -> head) && l == nil || 
             pt != &(box -> head) && l != nil) &&
            store(&(box -> ptail), struct sll **, pt) *
            sllbseg(&(box -> head), pt, l) *
            store(pt, struct sll *, 0)
    Ensure exists pt_new,
           __return != 0 &&
           store(&(__return -> ptail), struct sll **, pt_new) *
           sllbseg(&(__return -> head), pt_new, cons(data, l)) *
           store(pt_new, struct sll *, 0)
*/
{
  box->head = cons_list(data, box->head);
  if (box->ptail == &box->head) {
    box->ptail = &(box->head->next);
  }
  return box;
}
```

**功能**：在 List Box 头部插入新元素。

**核心逻辑**：
- 调用 `cons_list` 在头部插入节点
- **条件更新**：如果原本是空链表，更新 `ptail` 指向新节点的 `&next`

**验证分两个情况**（`sll_project_proof_manual.v`）：

1. **空链表情况**（`cons_list_box_return_wit_1`，第99行）：
   ```coq
   Exists (&(retval # "sll" ->ₛ "next")).
   ```
   - 原 `ptail` 指向 `&box->head`
   - 插入后 `ptail` 必须指向新节点的 `&next` 字段
   - 对应 C 代码第122-123行的指针更新

2. **非空链表情况**（`cons_list_box_return_wit_2`，第114行）：
   ```coq
   Exists pt.
   ```
   - `ptail` 已指向末尾节点的 `&next`，插入头部不影响尾指针
   - 链表段扩展一个节点，尾指针 `pt` 保持有效

#### 3.2.3 `map_list_box` - List Box 元素映射

```c
struct sllb *map_list_box(struct sllb *box, unsigned int x)
/*@ With l
    Require sllb_sll(box, l)
    Ensure sllb_sll(__return, map_mult(x, l))
*/
{
  map_list(box->head, x);
  return box;
}
```

**功能**：对 List Box 中的所有元素应用乘法映射。

**验证特性**：**完全自动化**，无需手动证明。

**验证流程**：

1. **入口展开（Strategy 35）**：
   ```coq
   sllb_sll(box, l) ⊢ exists h,
     store(&(box->head), h) * sll(h, l) * ...
   ```
   - 暴露内部链表 `sll h l` 和 `box->head`
   - 满足 `map_list` 的前置条件

2. **函数调用**：
   - `map_list(box->head, x)` 修改节点数据
   - 返回 `sll(h, map_mult(x, l))`

3. **返回折叠（Strategy 36）**：
   ```coq
   sll(h, map_mult(x, l)) ⊢ sllb_sll(box, map_mult(x, l))
   ```
   - 重新打包为 `sllb_sll`

**设计思想**：使用宽松谓词 `sllb_sll` 避免跟踪 `ptail` 精度，因为映射操作不改变链表结构。

#### 3.2.4 `free_list_box` - 释放 List Box

```c
void free_list_box(struct sllb *box)
/*@ With l
    Require sllb(box, l)
    Ensure emp
*/
{
  free_list(box->head);
  free_sllb(box);
}
```

**功能**：释放 List Box 及其内部链表。

**验证特性**：**完全自动化**，无需手动证明。

**验证流程**：

1. **资源分离（Strategy 32）**：
   ```coq
   sllb(box, l) ⊢ exists h pt,
     box->head == h && box->ptail == pt && sll(h, l)
   ```
   - 将 `sllb` 分解为容器字段和内容链表
   - 使用引理 `sllb_2_sll` 证明此蕴含关系

2. **资源消耗**：
   - `free_list(box->head)` 消耗 `sll(h, l)` 资源
   - `free_sllb(box)` 消耗 `box` 的字段资源

3. **返回验证**：
   - 所有资源释放完毕，剩余 `emp`
   - 满足后置条件

#### 3.2.5 `app_list_box` - sllb 合并

```c
struct sllb *app_list_box(struct sllb *b1, struct sllb *b2)
/*@ With l1 l2
    Require sllb(b1, l1) * sllb(b2, l2)
    Ensure sllb(__return, app(l1, l2))
*/
{
  struct sll *h2 = b2->head;
  struct sll **pt2 = b2->ptail;
  *(b1->ptail) = h2;              // 关键操作：将 b2 的头连接到 b1 的尾
  if (h2 != (struct sll *)0) {
    b1->ptail = pt2;              // 更新 b1 的尾指针为 b2 的尾指针
  }
  free_sllb(b2);
  return b1;
}
```

**功能**：将 List Box `b2` 合并到 `b1` 的尾部，常数时间完成。

**验证逻辑**（`sll_project_proof_manual.v`）：

1. **前置条件展开**（`app_list_box_which_implies_wit_1`，第162行）：
   ```coq
   sep_apply (sllb_2_sllbseg b1 l1).
   sep_apply (sllb_2_sll_pt b2 l2).
   ```
   - 将 `sllb(b1, l1)` 展开为 `sllbseg` 形式，暴露尾指针 `pt1`
   - 将 `sllb(b2, l2)` 展开为 `sll_pt` 形式，暴露头指针 `h2` 和尾指针 `pt2`

2. **非空情况合并**（`app_list_box_return_wit_2`，第150行）：
   ```coq
   sep_apply (sllbseg_append_sllbseg 
     (&(b1_pre # "sllb" ->ₛ "head")) pt1 l1 h2 pt2 z l2 H).
   sep_apply (sllbseg_2_sllb b1_pre pt2 (l1 ++ z :: l2) H0).
   ```
   - 第一步：证明指针更新 `*(b1->ptail) = h2` 的正确性，应用核心引理将两段链表逻辑连接
   - 第二步：重新折叠为 `sllb` 谓词，确认新的 `ptail = pt2` 满足不变量

3. **空链表情况**（`app_list_box_return_wit_1`）：
   - 当 `b2` 为空（`l2 = nil`），`b1` 的 `ptail` 保持不变

**核心引理**：`sllbseg_append_sllbseg`

```coq
sllbseg x pt1 l1 ** pt1 # Ptr |-> h2 ** sll_pt h2 pt2 l2
|-- sllbseg x pt2 (l1 ++ a :: l2)
```

- **基础情况**（`l1 = nil`）：`sllbseg x pt1 nil` 意味着 `x = pt1`，资源 `pt1 # Ptr |-> h2` 成为新链表段的头节点
- **归纳步骤**：展开 `l1 = h :: t`，对尾部 `t` 应用归纳假设，将连接点"拉链式"向后传递

#### 3.2.6 `sllb2array` - List Box 转数组

```c
unsigned int sllb2array(struct sllb *box, unsigned int **out_array)
/*@ With l
    Require sllb_sll(box, l) && Zlength(l) <= 2147483647 &&
            undef_data_at(out_array, unsigned int *)
    Ensure exists arr_ret,
           sllb_sll(box@pre, l) *
           store(out_array@pre, unsigned int *, arr_ret) *
           UIntArray::full_shape(arr_ret, Zlength(l))
*/
{
  return sll2array(box->head, out_array);
}
```

**功能**：将 List Box 转换为数组，内部调用 `sll2array`。

**验证特性**：简单包装函数，通过策略35展开 `sllb_sll` 后调用辅助函数。

---

## 4. 验证架构

### 4.1 文件组织

| 文件 | 内容 |
|------|------|
| `sll_project_lib.v` | 谓词定义、引理库 |
| `sll_project_lib.c` | C 源代码 + 形式化规约（注释） |
| `sll_project.strategies` | 策略规则定义 |
| `sll_project_strategy_proof.v` | 策略正确性证明 |
| `sll_project_proof_manual.v` | 核心函数手动证明 |
| `sll_project_proof_auto.v` | 自动生成的证明框架 |

### 4.2 策略分类

策略分为以下类别：
- **sll 基础**（3-7）：标准链表性质
- **sllseg 段操作**（14-16）：链表段分割合并
- **sllbseg 尾指针段**（20-22）：List Box 专用段操作
- **sllb / sllb_sll 视图转换**（30-38）：精确/宽松谓词转换
- **链表操作**（40-61）：长度、映射、合并等
- **数组操作**（70-93）：数组分配、边界、形状转换

## 5. 文档资源

- **[sllb_lemmas_guide.md](sllb_lemmas_guide.md)**：引理详细文档
- **[app_list_box_verification_notes.md](app_list_box_verification_notes.md)**：合并函数验证笔记
- **[sllb2array_verification_notes.md](sllb2array_verification_notes.md)**：数组转换验证笔记
- **[precision_problem_analysis.md](precision_problem_analysis.md)**：分离逻辑精确性问题分析
- **[SubmissionFiles/](SubmissionFiles/)**：所有关键文件汇总

更详细的构建说明请参考[主 README](../README.md)。

