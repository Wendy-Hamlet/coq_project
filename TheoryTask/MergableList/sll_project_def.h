struct sll {
    unsigned int data;
    struct sll * next;
};

struct sllb {
    struct sll * head;
    struct sll ** ptail;
};

/*@ Import Coq Require Import sll_project_lib */

/*@ Extern Coq (sll : Z -> list Z -> Assertion) */
/*@ Extern Coq (sllseg : Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (sllbseg : Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (sllb : Z -> list Z -> Assertion) */
/*@ Extern Coq (map_mult : Z -> list Z -> list Z) */

/*@ Extern Coq (UIntArray::full : Z -> Z -> list Z -> Assertion)
               (UIntArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (UIntArray::undef_full : Z -> Z -> Assertion)
               (UIntArray::undef_ceil : Z -> Z -> Z -> Assertion)
               (UIntArray::undef_missing_i : Z -> Z -> Z -> Z -> Assertion)
               (UIntArray::ceil_shape : Z -> Z -> Z -> Assertion)
               (UIntArray::full_shape : Z -> Z -> Assertion)
               (Znth : {A} -> Z -> list A -> A -> A)
               (replace_Znth : {A} -> Z -> A -> list A -> list A)
*/

/*@ include strategies "sll_project.strategies" */
