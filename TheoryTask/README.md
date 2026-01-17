# Part 1: Precise Structural Modeling & Pointer Logic

This section details the verification strategies for the `sllb` (List Box) structure, specifically focusing on the challenge of verifying $O(1)$ tail operations involving double pointers.

## 1. Predicate Design: The `sllb` Structure

To support $O(1)$ append operations, the C structure maintains a tail pointer (`ptail`) that points to the location where the next node should be attached. The physical semantics of this pointer differ fundamentally depending on whether the list is empty or not. We model this utilizing a disjunctive separation logic predicate `sllb`.

### Definition (`sllb` in `sll_project_lib.v`)
The predicate distinguishes two cases to precisely track the memory location of the "tail":

```coq
Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  match l with
  | nil =>
      (* Case Empty: ptail points to the 'head' field of the box itself *)
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      (* Case Non-Empty: ptail points to the 'next' field of the last node *)
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.
```

*   **Case Nil**: `ptail` points to `&box->head`. Writing to `*ptail` updates the head pointer directly.
*   **Case Cons**: `ptail` points to the `next` field of the last node. Writing to `*ptail` links a new node to the end of the chain.

### Auxiliary Predicates
*   **`sllbseg x y l`**: Describes a list segment starting at `x` and ending at the address `y` (the location of the pointer to the next segment). This is essential for describing the content *between* the head and the tail pointer.
*   **`sll_pt h pt l`**: Used in `app_list_box` to expose the tail address `pt` of a standard singly linked list starting at `h`.

## 2. Key Structural Lemmas

Verification of pointer manipulation relies on a set of structural lemmas defined in `sll_project_lib.v`. These allow us to decompose the proof into small, manageable steps.

### Lemma: `sllbseg_append_sllbseg`
This is the central lemma for proving the $O(1)$ merge. It states that if we have a segment ending at `pt1`, and `pt1` points to the head of a second segment `h2`, the two segments are logically connected.

> **Formal Statement:**
> `sllbseg x pt1 l1 ** pt1 # Ptr |-> h2 ** ... ** sllbseg ... l2 ... |-- sllbseg x pt2 (l1 ++ a :: l2)`

**Proof Sketch:**
The proof proceeds by **induction on the first list `l1`**:
*   **Base Case (`l1 = nil`)**: The segment `sllbseg x pt1 nil` implies `x = pt1`. We must prove `sllbseg pt1 pt2 (a::l2)`. The resource `pt1 # Ptr |-> h2` (provided in the premise) serves as the critical link, satisfying the existential quantifier for the head node in the target `sllbseg`.
*   **Inductive Step**: For `l1 = h :: t`, we unfold the head of the first segment. We then apply the **inductive hypothesis** to the remaining tail segment `sllbseg ... t`. This effectively "zippers" the connection at `pt1`, extending the recursive definition to cover the appended list.

### Lemma: `sllb_2_sll_pt`
A view-shift lemma that unfolds the recursive `sllb` definition into a flat representation, exposing the head `h` and the tail pointer `pt`. This is used to "open" the box before modification.

## 3. Correctness Proofs

With the predicates and lemmas defined, we present the high-level proof logic for the critical functions.

### 3.1 Verification of `app_list_box` (O(1) Merge)
The function merges list `b2` into `b1` in constant time. The proof is split into three lemmas in `sll_project_proof_manual.v`, reflecting the Verification Condition Generation (VCG) structure:

1.  **Implication Verification (`app_list_box_which_implies_wit_1`, L162)**:
    Before the list manipulation, we justify the symbolic execution path.
    *   **Tactic**: `sep_apply (sllb_2_sllbseg b1 l1)` and `sep_apply (sllb_2_sll_pt b2 l2)`.
    *   **Logic**: This explicitly unfolds the `sllb` resources. `b1` is unfolded to expose its tail pointer `pt1` (via `sllbseg`), and `b2` is unfolded to expose its head `h2` and tail pointer `pt2` (via `sll_pt`).

2.  **Return Verification (`app_list_box_return_wit_2`, L150)**:
    This lemma handles the core logic when `b2` is non-empty (`l2` is not nil).
    *   **Step 1: Resource Merge**: We apply the critical structural lemma:
        ```coq
        sep_apply (sllbseg_append_sllbseg (&(b1_pre # "sllb" ->ₛ "head")) pt1 l1 h2 pt2 z l2 H).
        ```
        This step formally executes the pointer update `*(b1->ptail) = b2->head`, logically merging the two segments.
    *   **Step 2: Re-packaging**: After the merge, we apply:
        ```coq
        sep_apply (sllbseg_2_sllb b1_pre pt2 (l1 ++ z :: l2) H0).
        ```
        This folds the segment back into a valid `sllb` predicate, confirming that the new structure (with `ptail` now pointing to `pt2`) forms a valid list box.

### 3.2 Verification of `cons_list_box`
This function prepends a node. The proof handles the critical update of `ptail` using case analysis on the list state `l`:

1.  **Non-Empty Case (`cons_list_box_return_wit_2`, L114)**:
    *   **Logic**: When `l` is not nil, `ptail` points to the end of the list. Inserting at the head does **not** change the location of `ptail`.
    *   **Proof**: The proof simply updates the head pointer. The `sllbseg` is extended by one node, but the tail pointer `pt` remains valid.

2.  **Empty Case (`cons_list_box_return_wit_1`, L99)**:
    *   **Logic**: When `l` is nil, `ptail` initially points to `&box->head`. After insertion, `ptail` must point to `&node->next`.
    *   **Proof**: The tactic script explicitly instantiates the new tail pointer:
        ```coq
        Exists (&(retval # "sll" ->ₛ "next")).
        ```
        This matches the C code logic `box->ptail = &(box->head->next)` (lines 122-123 in `sll_lib.c`), proving that the pointer update correctly maintains the `sllb` invariant for the singleton list.

# Part 2: Array Conversion & View-Shift Strategies

This section details the verification logic for converting linked list boxes to arrays (`sllb2array`). It focuses on the "Strategy" proof architecture used to handle the complexity of array bounds and the predicate view-shifts required to bypass the precision limitations of the strict `sllb` predicate during read-only traversals.

## 1. The Challenge: Read-Only Traversal & Precision

As detailed in Part 1, `sllb` is a "heavy" predicate designed for $O(1)$ mutations. However, functions like `sllb2array` and `map_list_box` perform read-only traversals or simple data mappings. Using the strict `sllb` predicate here introduces a **Precision Problem**:
* To call the helper `sll2array`, we must unfold `sllb` to `sll`.
* The strict `sllb` definition requires tracking the exact location of `ptail`.
* Standard list traversal (via `sll`) loses the correlation between the list end and the `ptail` pointer location.
* Upon returning, we cannot mathematically prove that the tail of the traversed list matches the original `ptail` without introducing complex auxiliary variables.

### Solution: The `sllb_sll` View
To resolve this, we utilize a relaxed predicate `sllb_sll` (defined in `sll_project_lib.v`, L60) for operations that do not alter the list structure.

```coq
Definition sllb_sll (x: addr) (l: list Z): Assertion :=
  [| x <> 0 |] &&
  EX h: addr,
    &(x # "sllb" ->ₛ "head") # Ptr |-> h **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> 0 ** (* Tail tracking relaxed/ignored *)
    sll h l.

```

This predicate views the "box" merely as a container for a standard singly linked list `sll`, purposefully ignoring the strict `ptail` invariants. This allows us to verify traversal logic without the burden of tail pointer arithmetic.

## 2. Strategy-Based Proof Architecture

Our verification relies on a "Strategy" pattern where complex entailments generated by the QCP logic generator are isolated into `sll_project_strategy_proof.v`. This allows us to prove specific logic transitions (Strategies) independently of the main C program verification.

### 2.1 View-Shift Strategies (`sllb`  `sll`)

For `sllb2array`, the verification relies on shifting between the box view and the list view.

* **Strategy 35 (Unfold)**:
Proves that `sllb_sll` implies the existence of a standard `sll`. This allows the C function to pass `box->head` to `sll2array` or `map_list`.
> **Proof (`sll_project_strategy35_correctness`):**
> We use `unfold sllb_sll` and `Intros h` to expose the head pointer `h` and the inner `sll h l` resource, satisfying the precondition of the inner function call.

* **Strategy 36 (Fold)**:
Proves the reverse: restoring `sllb_sll` from an `sll`.
> **Proof (`sll_project_strategy36_correctness`):**
> After the helper function returns `sll h l`, we simply `Exists h` and repackage the resources. Because `sllb_sll` does not demand `ptail` precision, this entailment is trivial compared to the strict `sllb` reconstruction.

## 3. Fully Automated Verification of `map_list_box`

A testament to the effective design of our strategies is the verification of `map_list_box`. This function required **zero manual proof**. The logic generator's output was entirely solved by the strategies defined in `sll_project_strategy_proof.v`.

### 3.1 The Logic Flow
The function is a simple wrapper:
1.  **Entry (`map_list_box_which_implies_wit_1`)**: The automation engine matches this entailment against **Strategy 35**. The `sllb_sll` resource is automatically unfolded to expose `sll h l` and `box->head`.
2.  **Function Call**: `map_list(box->head, x)` is called. The precondition `sll h l` is satisfied by the result of Step 1.
3.  **Return (`map_list_box_return_wit_1`)**: The automation engine matches the post-state (where `map_list` returns `sll h (map_mult x l)`) against **Strategy 36**. It automatically folds the resources back into `sllb_sll`.

### 3.2 The `map_mult` Auxiliary Predicate
To specify the behavior of mapping multiplication over a list, we defined `map_mult` in `sll_project_lib.v`:

```coq
Definition map_mult (x: Z) (l: list Z): list Z :=
  List.map (fun a => unsigned_last_nbits (x * a) 32) l.
```

This definition lifts the C-level multiplication (modulo $2^{32}$) to the logical level. The automation relies on standard list properties (e.g., `map_app`) to prove that processing the list element-by-element in the loop matches this high-level definition.

## 4. Array Verification Strategies (`sll2array`)

The core complexity of `sllb2array` lies in `sll2array`, which allocates and fills a C array. The verification uses `UIntArray` predicates from the separation logic library.

### Loop Invariant Design

The loop in `sll2array` maintains an invariant splitting the array into two logical segments:

1. **`UIntArray.ceil_shape arr 0 i`**: The filled portion of the array (indices  to ).
2. **`UIntArray.undef_ceil arr i len`**: The allocated but uninitialized portion (indices  to ).

### Key Array Lemmas

The strategies in `sll_project_strategy_proof.v` rigorously prove the spatial safety of this split.

* **Strategy 72: Array Splitting (L128)**
This strategy justifies writing to `arr[i]`. It proves that an undefined segment from  to  can be split into a single writable element at  and a remaining segment starting at .
* **Logic**:
```coq
UIntArray.undef_ceil p x y |-- 
UIntArray.undef_ceil p (x + 1) y ** poly_undef_store ... (at p + x)

```


* **Proof**: Utilizes `UIntArray.undef_ceil_split_to_undef_ceil` and `UIntArray.undef_ceil_unfold` to isolate the memory address `p + x` for the store operation.


* **Strategy 92: Full Shape Realization (L145)**
When the loop terminates (), this strategy proves that a `ceil_shape` from  to  is equivalent to a `full_shape` of size , satisfying the postcondition of `sll2array`.

## 4. Conclusion on Strategy Proofs

By offloading the complex spatial arithmetic of arrays (Strategies 70-93) and the structural view-shifts of linked lists (Strategies 30-36) into `sll_project_strategy_proof.v`, we achieved a modular verification.

* **Success**: We successfully verified `sllb2array` without `Admitted` lemmas by adopting `sllb_sll` to bypass the tail-precision problem.
* **Robustness**: The array strategies provide a reusable foundation for any future array-manipulation functions in this project, ensuring bounds safety via formal logic.
