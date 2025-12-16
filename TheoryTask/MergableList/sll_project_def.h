struct sll {
    unsigned int data;
    struct sll * next;
};

struct sllb {
    struct sll * head;
    struct sll ** ptail;
};

/*@ Import Coq Require Import sll_project_lib */

// sll predicates
/*@ Extern Coq (sll : Z -> list Z -> Assertion) */
/*@ Extern Coq (sllseg : Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (sllbseg : Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (sllb : Z -> list Z -> Assertion) */
/*@ Extern Coq (map_mult : Z -> list Z -> list Z) */

// UIntArray predicates
/*@ Extern Coq (UIntArray::full : Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (UIntArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (UIntArray::undef_full : Z -> Z -> Assertion) */
/*@ Extern Coq (UIntArray::undef_ceil : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (UIntArray::undef_missing_i : Z -> Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (UIntArray::ceil_shape : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (UIntArray::full_shape : Z -> Z -> Assertion) */

// Utility functions
/*@ Extern Coq (Znth : {A} -> Z -> list A -> A -> A) */
/*@ Extern Coq (replace_Znth : {A} -> Z -> A -> list A -> list A) */

/*@ include strategies "sll_project.strategies" */
