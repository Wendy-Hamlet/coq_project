## 2. Strategy Design and Rationale

### 2.1 Overview
The strategy files define the entailment rules required by the QCP verification framework to support symbolic execution. This section outlines the design rationale for the strategies corresponding to the basic linked list predicates (`sll`, `sllseg`), the simplified list box predicate (`sllb_sll`), and the array predicates (`UIntArray`). The primary objective is to establish sound mappings between abstract predicates and the low-level heap memory model.

### 2.2 Predicate Abstraction and Conversion
To optimize verification efficiency, the design distinguishes between structural modifications and read-only traversals of the list box structure.

* **Logic Simplification for Read-Only Contexts**: The `sllb` structure contains a double pointer `ptail` to track the list tail efficiently. However, functions such as `map_list_box` or `sllb2array` do not modify the structural integrity of the list, making the precise tracking of `ptail` redundant for their verification.
* **Strategy Implementation**: Strategies 35 and 36 are designed to facilitate the conversion between the strict `sllb` predicate and the simplified `sllb_sll` predicate. `sllb_sll` abstracts the list box as a container holding a head pointer to a standard `sll`, ignoring the `ptail` constraint. This allows the verification logic to leverage standard `sll` lemmas for traversal operations without managing the complexity of the `ptail` invariant.

### 2.3 Inductive Structure Unfolding
The verification of loops and recursive functions requires the logic engine to dynamically unfold inductive definitions into their constituent heap elements.

* **List Unfolding**: Strategies 3, 4, 5, and 6 establish the logical equivalence between the `sll` predicate and its heap representation. These strategies formally define that a non-empty `sll` consists of a data field, a next pointer, and a recursive tail segment. This ensures that the symbolic execution engine can safely access node members during iteration.
* **Segment Properties**: Strategy 14 establishes the reflexive property of list segments (`sllseg`). By proving that a segment from a pointer to itself equates to an empty heap (`emp`), this strategy provides the necessary base case for loop invariant establishment.

### 2.4 Array Memory Model
The verification of array-related functions (e.g., `sll2array`) relies on `UIntArray` predicates to model contiguous memory blocks.

* **Range Decomposition**: Strategies 70 through 72 define the rules for splitting and merging array permissions. The design ensures that a `undef_full` or `undef_ceil` predicate implies permission to access specific indexed elements while maintaining the generated proofs for the remaining memory segments. This logic supports the verification of memory safety and bounds checking during array population.

### 2.5 Proof Methodology
The correctness of the aforementioned strategies is formally verified in `sll_project_strategy_proof.v`. The proofs rely on auxiliary lemmas defined in the library (e.g., `sll_zero`, `sllseg_0_sll`, `sllb_2_sll`) to demonstrate that the entailments hold under Separation Logic. The proofs confirm that the view conversions and structural unfoldings preserve memory safety properties without introducing unsound assumptions.


## 3. Verification of Core Logic

This section details the verification of the main functional logic, focusing on how the strategies defined in the previous section are applied to verify loop invariants, memory safety for arrays, and function wrappers.

### 3.1 Loop Invariant Verification
For functions involving iteration, such as `map_list` and `sll_length`, the core challenge lies in defining and maintaining loop invariants. The verification utilizes the list segment predicate `sllseg` to describe the partial structures formed during traversal.

* **Invariant Construction**: The loop invariant typically partitions the list into two parts: a processed segment described by `sllseg(head, p, l1)` and a remaining list described by `sll(p, l2)`.
* **Strategy Application**: 
    * Upon entering the loop, strategy entailments allow the decomposition of the full list into an empty segment and the full list.
    * During iteration, the transitivity property of `sllseg` (as supported by Strategy 14) is used to append the newly processed node to the existing segment.
    * At loop termination, the logic proves that the `sllseg` covers the entire list, ensuring that all elements have been correctly processed or counted.

### 3.2 Array Operation Verification
The function `sll2array` involves converting a linked list to a contiguous integer array. The verification must ensure that array writes do not exceed allocated bounds.

* **Memory Modeling**: The `UIntArray` predicates (`undef_full`, `undef_ceil`) are used to model the array's memory state. The assertions explicitly track the initialization status of the array elements.
* **Split and Merge Strategies**: To verify the assignment `arr[i] = p->data`, strategies 70-72 are applied to split the array permission. The proof demonstrates that `undef_ceil(p, 0, n)` implies the existence of a specific writable location `p + i` and the remaining undefined segments. This rigorous splitting guarantees that index `i` is strictly within the valid range derived from the list length.

### 3.3 Abstract View for Wrapper Functions
Wrapper functions like `sllb2array` and `map_list_box` provide interfaces for `sllb` structures but delegate the actual processing to `sll`-based functions.

* **View Shifting Verification**: The proofs for these functions utilize the "View Shifting" strategies established in the design phase. 
* **Process**:
    1.  **Pre-call**: The proof applies an entailment (e.g., Strategy 35) to convert the input `sllb` (which tracks `ptail`) into an `sllb_sll` (which only exposes `head`).
    2.  **Execution**: The underlying functions (`sll2array` or `map_list`) are called using the simpler `sll` specification.
    3.  **Post-call**: Since these functions do not alter the list structure, the return state can be safely entailed back to the `sllb` form (if required) or maintained as `sllb_sll` for the post-condition, avoiding the complexity of reconstructing the `ptail` pointer relationship.





`(不知道最后要啥语言所以再附一个中文版)`

## 2. 策略设计与设计原理

### 2.1 概述
策略文件定义了 QCP 验证框架支持符号执行所需的蕴含规则。本节概述了对应于基础链表谓词（`sll`、`sllseg`）、简化版链表盒子谓词（`sllb_sll`）以及数组谓词（`UIntArray`）的策略设计原理。主要目标是在抽象谓词与底层堆内存模型之间建立健全的映射关系。

### 2.2 谓词抽象与转换
为了优化验证效率，设计中区分了对链表盒子结构的“结构性修改”与“只读遍历”。

* **只读上下文的逻辑简化**：`sllb` 结构体包含一个双重指针 `ptail` 以高效追踪链表尾部。然而，诸如 `map_list_box` 或 `sllb2array` 等函数并不修改链表的结构完整性，这使得在验证它们时精确追踪 `ptail` 显得多余。
* **策略实现**：策略 35 和 36 旨在促进严格的 `sllb` 谓词与简化的 `sllb_sll` 谓词之间的转换。`sllb_sll` 将链表盒子抽象为一个仅持有指向标准 `sll` 头指针的容器，忽略了 `ptail` 约束。这允许验证逻辑在不管理 `ptail` 不变式复杂性的情况下，利用标准 `sll` 引理进行遍历操作。

### 2.3 归纳结构的展开
循环和递归函数的验证要求逻辑引擎能够将归纳定义动态展开为其组成的堆元素。

* **链表展开**：策略 3、4、5 和 6 建立了 `sll` 谓词与其堆表示之间的逻辑等价性。这些策略形式化地定义了非空 `sll` 由数据域、next 指针和递归尾部段组成。这确保了符号执行引擎在迭代期间可以安全地访问节点成员。
* **片段性质**：策略 14 建立了链表段（`sllseg`）的自反性质。通过证明从指针指向其自身的段等价于空堆（`emp`），该策略为建立循环不变式提供了必要的基准情况。

### 2.4 数组内存模型
数组相关函数（例如 `sll2array`）的验证依赖于 `UIntArray` 谓词来对连续内存块进行建模。

* **范围分解**：策略 70 至 72 定义了拆分与合并数组权限的规则。该设计确保了 `undef_full` 或 `undef_ceil` 谓词蕴含了访问特定索引元素的权限，同时保留了剩余内存段的生成证明。此逻辑支持了数组填充期间的内存安全验证和边界检查。

### 2.5 证明方法
上述策略的正确性已在 `sll_project_strategy_proof.v` 中得到形式化验证。证明依赖于库中定义的辅助引理（例如 `sll_zero`、`sllseg_0_sll`、`sllb_2_sll`）来证明在分离逻辑下蕴含关系成立。这些证明确认了视图转换和结构展开在不引入不健全假设的情况下保留了内存安全属性。

## 3. 核心逻辑验证

本节详细介绍了主要功能逻辑的验证，重点阐述如何应用上一节定义的策略来验证循环不变式、数组内存安全以及封装函数。

### 3.1 循环不变式验证
对于涉及迭代的函数，如 `map_list` 和 `sll_length`，核心挑战在于定义和维护循环不变式。验证利用链表段谓词 `sllseg` 来描述遍历过程中形成的部分结构。

* **不变式构造**：循环不变式通常将链表划分为两部分：由 `sllseg(head, p, l1)` 描述的已处理段，以及由 `sll(p, l2)` 描述的剩余链表。
* **策略应用**：
    * 进入循环时，策略蕴含规则允许将完整链表分解为一个空段和完整链表。
    * 迭代期间，利用 `sllseg` 的传递性（由策略 14 支持）将新处理的节点追加到现有段中。
    * 循环终止时，逻辑证明 `sllseg` 覆盖了整个链表，确保所有元素都已被正确处理或计数。

### 3.2 数组操作验证
函数 `sll2array` 涉及将链表转换为连续的整型数组。验证必须确保数组写入操作不超过分配的边界。

* **内存建模**：`UIntArray` 谓词（`undef_full`、`undef_ceil`）用于对数组的内存状态进行建模。断言显式追踪了数组元素的初始化状态。
* **拆分与合并策略**：为了验证赋值语句 `arr[i] = p->data`，应用策略 70-72 来拆分数组权限。证明表明 `undef_ceil(p, 0, n)` 蕴含了特定可写位置 `p + i` 以及剩余未定义段的存在。这种严格的拆分保证了索引 `i` 严格处于从链表长度推导出的有效范围内。

### 3.3 封装函数的抽象视图
诸如 `sllb2array` 和 `map_list_box` 等封装函数为 `sllb` 结构提供了接口，但将实际处理委托给基于 `sll` 的函数。

* **视图转换验证**：这些函数的证明利用了设计阶段建立的“视图转换”策略。
* **过程**：
    1.  **调用前**：证明应用蕴含规则（例如策略 35）将输入 `sllb`（追踪 `ptail`）转换为 `sllb_sll`（仅暴露 `head`）。
    2.  **执行**：使用较简单的 `sll` 规范调用底层函数（`sll2array` 或 `map_list`）。
    3.  **调用后**：由于这些函数不改变链表结构，返回状态可以安全地蕴含回 `sllb` 形式（如果需要）或保持为 `sllb_sll` 作为后置条件，从而避免了重建 `ptail` 指针关系的复杂性。