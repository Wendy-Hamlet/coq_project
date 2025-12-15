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

/*@ include strategies "sll_project.strategies" */
