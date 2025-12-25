Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

(* ============================================================ *)
(* sll: singly linked list *)
(* ============================================================ *)

Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX y: addr,
                   &(x # "sll" ->ₛ "data") # UInt |-> a **
                   &(x # "sll" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

(* ============================================================ *)
(* sllseg: segment of singly linked list *)
(* ============================================================ *)

Fixpoint sllseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = y |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX z: addr,
                   &(x # "sll" ->ₛ "data") # UInt |-> a **
                   &(x # "sll" ->ₛ "next") # Ptr |-> z **
                   sllseg z y l0
  end.

(* ============================================================ *)
(* sllbseg: segment for list box (stores pointer to node) *)
(* ============================================================ *)

Fixpoint sllbseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = y |] && emp
    | a :: l0 => EX z: addr,
                   [| z <> NULL |] &&
                   x # Ptr |-> z **
                   &(z # "sll" ->ₛ "data") # UInt |-> a **
                   sllbseg (&(z # "sll" ->ₛ "next")) y l0
  end.

(* ============================================================ *)
(* sllb: list box containing singly linked list *)
(*   Design inspired by sll_queue: split empty/non-empty cases *)
(*   - Empty: head = NULL, ptail = &head (explicit resources) *)
(*   - Non-empty: use sllbseg (first element guarantees &head resource) *)
(* ============================================================ *)

Definition sllb (x: addr) (l: list Z): Assertion :=
  [| x <> NULL |] &&
  match l with
  | nil =>
      (* Empty list: explicit resources, no sllbseg *)
      (* Key: &(x->head) |-> NULL is explicitly provided *)
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      (* Non-empty list: sllbseg provides &(x->head) |-> h *)
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.

(* ============================================================ *)
(* map_mult: multiply each element by x *)
(* ============================================================ *)

Definition map_mult (x: Z) (l: list Z): list Z :=
  List.map (fun a => unsigned_last_nbits (x * a) 32) l.

Lemma map_mult_nil: forall x, map_mult x nil = nil.
Proof. reflexivity. Qed.

Lemma map_mult_cons: forall x a l,
  map_mult x (a :: l) = (unsigned_last_nbits (x * a) 32) :: map_mult x l.
Proof. reflexivity. Qed.

(* ============================================================ *)
(* Lemmas for sll *)
(* ============================================================ *)

Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- [| l = nil |] && emp.
Proof.
  intros. destruct l.
  + entailer!.
  + simpl. Intros. Intros x0. entailer!.
Qed.

Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      [| l = a :: l0 |] &&
      &(x # "sll" ->ₛ "data") # UInt |-> a **
      &(x # "sll" ->ₛ "next") # Ptr |-> y **
      sll y l0.
Proof.
  intros. destruct l.
  + simpl. Intros. tauto.
  + simpl. Intros. Intros y. Exists y z l. entailer!.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- [| l <> nil |].
Proof.
  intros. destruct l.
  + simpl. Intros. tauto.
  + simpl. Intros. Intros y. entailer!. congruence.
Qed.

Lemma sll_not_null_length: forall p l,
  p <> NULL ->
  sll p l |-- [| Zlength l >= 1 |].
Proof.
  intros. destruct l.
  - simpl sll. Intros. contradiction.
  - simpl sll. Intros. entailer!.
    rewrite Zlength_cons. pose proof Zlength_nonneg l. lia.
Qed.

(* ============================================================ *)
(* Lemmas for sllseg *)
(* ============================================================ *)

Lemma sllseg_len1: forall x a y,
  x <> NULL ->
  &(x # "sll" ->ₛ "data") # UInt |-> a **
  &(x # "sll" ->ₛ "next") # Ptr |-> y |--
  sllseg x y [a].
Proof.
  intros. simpl sllseg. Exists y. entailer!.
Qed.

Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
Proof.
  intros. revert x; induction l1; simpl sllseg; intros.
  + Intros. subst y. entailer!.
  + Intros. Intros z0. Exists z0. sep_apply IHl1. entailer!.
Qed.

Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
Proof.
  intros. revert x; induction l1; simpl sllseg; simpl sll; intros.
  + Intros. subst y. entailer!.
  + Intros. Intros z0. Exists z0. sep_apply IHl1. entailer!.
Qed.

Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
Proof.
  intros. revert x. induction l; try easy.
  simpl. intros. Intros z. Exists z. entailer!.
Qed.

(* ============================================================ *)
(* Lemmas for sllbseg *)
(* ============================================================ *)

Lemma sllbseg_len1: forall (x y: addr) (a: Z),
  y <> 0 ->
  x # Ptr |-> y **
  &(y # "sll" ->ₛ "data") # UInt |-> a |--
  sllbseg x (&(y # "sll" ->ₛ "next")) [a].
Proof.
  intros. simpl. Exists y. entailer!.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros. revert x; induction l1; simpl; intros.
  + entailer!. subst x. entailer!.
  + Intros u. Exists u. entailer!.
Qed.

Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
Proof.
  intros. revert x; induction l; simpl; intros.
  + Intros. subst x. Exists z; entailer!.
  + Intros x_v. Exists x_v. sep_apply IHl. Intros y'. Exists y'. entailer!.
Qed.

Lemma sllbseg_0_sll': forall x y l,
  sllbseg x y l ** y # Ptr |-> NULL |--
  EX head_val: addr, x # Ptr |-> head_val ** sll head_val l.
Proof.
  intros. revert x; induction l; simpl; intros.
  + Intros. subst x. Exists NULL. simpl sll. entailer!.
  + Intros head_val. Exists head_val.
    sep_apply IHl. Intros next_val. simpl sll. Exists next_val. entailer!.
Qed.

Lemma sllbseg_sll': forall x y l1 l2,
  sllbseg x y l1 ** y # Ptr |-> 0 ** sll 0 l2 |--
  EX h: addr, x # Ptr |-> h ** sll h (l1 ++ l2).
Proof.
  intros.
  assert (H0: (0:addr) = NULL) by reflexivity.
  sep_apply (sll_zero 0 l2 H0). Intros. subst l2.
  rewrite app_nil_r. sep_apply sllbseg_0_sll'.
  Intros head_val. Exists head_val. entailer!.
Qed.

Lemma sllbseg_sll: forall x y z l1 l2,
  sllbseg x y l1 ** y # Ptr |-> z ** sll z l2 |--
  EX h: addr, x # Ptr |-> h ** sll h (l1 ++ l2).
Proof.
  intros.
  sep_apply sllbseg_2_sllseg. Intros y'.
  Exists y'. sep_apply sllseg_sll. entailer!.
Qed.

(* ============================================================ *)
(* Lemmas for sllb *)
(* ============================================================ *)

Lemma sllb_zero: forall x,
  sllb x nil |--
  [| x <> NULL |] &&
  &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> &(x # "sllb" ->ₛ "head").
Proof.
  intros. unfold sllb. simpl. entailer!.
Qed.

Lemma sllb_not_zero: forall x a l,
  sllb x (a :: l) |--
  EX head_val ptail_val: addr,
    [| x <> NULL |] &&
    [| head_val <> NULL |] &&
    &(x # "sllb" ->ₛ "head") # Ptr |-> head_val **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    &(head_val # "sll" ->ₛ "data") # UInt |-> a **
    sllbseg (&(head_val # "sll" ->ₛ "next")) ptail_val l **
    ptail_val # Ptr |-> NULL.
Proof.
  intros. unfold sllb.
  Intros ptail_val. simpl sllbseg. Intros head_val.
  Exists head_val ptail_val. entailer!.
Qed.

Lemma sllb_len1: forall x,
  x <> NULL ->
  &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> &(x # "sllb" ->ₛ "head") |--
  sllb x nil.
Proof.
  intros. unfold sllb. simpl. entailer!.
Qed.

Lemma sllb_2_sllbseg: forall x l,
  sllb x l |--
  EX ptail_val: addr,
    [| x <> NULL |] &&
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
    ptail_val # Ptr |-> NULL.
Proof.
  intros. unfold sllb. destruct l.
  + (* nil case *)
    Exists (&(x # "sllb" ->ₛ "head")).
    simpl sllbseg. entailer!.
  + (* cons case *)
    Intros ptail_val. Exists ptail_val. entailer!.
Qed.

Lemma sllb_2_sll: forall x l,
  sllb x l |--
  EX head_val ptail_val: addr,
    [| x <> NULL |] &&
    &(x # "sllb" ->ₛ "head") # Ptr |-> head_val **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sll head_val l.
Proof.
  intros. unfold sllb. destruct l.
  + (* nil case *)
    Exists NULL (&(x # "sllb" ->ₛ "head")).
    simpl sll. entailer!.
  + (* cons case *)
    Intros ptail_val. sep_apply sllbseg_0_sll'.
    Intros head_val. Exists head_val ptail_val. entailer!.
Qed.

Lemma sllbseg_2_sllb: forall x ptail_val l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
  sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
  ptail_val # Ptr |-> NULL |--
  sllb x l.
Proof.
  intros. unfold sllb. destruct l.
  + (* nil case *)
    simpl sllbseg. Intros. subst ptail_val. entailer!.
  + (* cons case *)
    Exists ptail_val. entailer!.
Qed.

Lemma sll_2_sllbseg: forall x h l,
  x # Ptr |-> h ** sll h l |--
  EX pt: addr, sllbseg x pt l ** pt # Ptr |-> NULL.
Proof.
  intros. revert x h; induction l; simpl; intros.
  + Intros. subst h. Exists x. simpl sllbseg. entailer!.
  + Intros. Intros next.
    sep_apply (IHl (&(h # "sll" ->ₛ "next")) next).
    Intros pt. Exists pt. simpl sllbseg. Exists h. entailer!.
Qed.

Lemma sll_2_sllb: forall x h l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "head") # Ptr |-> h ** sll h l |--
  EX ptail_new: addr,
    sllbseg (&(x # "sllb" ->ₛ "head")) ptail_new l **
    ptail_new # Ptr |-> NULL.
Proof.
  intros.
  sep_apply (sll_2_sllbseg (&(x # "sllb" ->ₛ "head")) h l).
  Intros pt_new. Exists pt_new. entailer!.
Qed.

(* ============================================================ *)
(* Additional lemmas for app_list_box *)
(* ============================================================ *)

(* When h2 = 0, l2 must be nil *)
Lemma sll_zero_nil: forall h l,
  h = NULL ->
  sll h l |-- [| l = nil |].
Proof.
  intros. destruct l.
  + entailer!.
  + simpl. Intros. Intros y. entailer!.
Qed.

(* Rebuild sllb from store + sll after appending nil *)
Lemma store_sll_2_sllb: forall x h pt l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "head") # Ptr |-> h **
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
  sll h l |--
  EX pt_new: addr,
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
    sllbseg (&(x # "sllb" ->ₛ "head")) pt_new l **
    pt_new # Ptr |-> NULL.
Proof.
  intros.
  sep_apply (sll_2_sllb x h l H).
  Intros ptail_new.
  Exists ptail_new.
  entailer!.
Qed.

(* Full reconstruction of sllb from store + sll *)
Lemma store_sll_2_sllb_full: forall x h l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "head") # Ptr |-> h **
  sll h l |--
  EX pt_new: addr,
    sllbseg (&(x # "sllb" ->ₛ "head")) pt_new l **
    pt_new # Ptr |-> NULL.
Proof.
  intros.
  sep_apply (sll_2_sllb x h l H).
  Intros ptail_new.
  Exists ptail_new.
  entailer!.
Qed.

(* Connecting two slls via a pointer write *)
Lemma sll_connect: forall h1 l1 h2 l2 pt,
  sll h1 l1 ** pt # Ptr |-> h2 ** sll h2 l2 |--
  EX h_new: addr,
    sll h1 l1 ** pt # Ptr |-> h2 ** sll h2 l2.
Proof.
  intros.
  Exists h1. entailer!.
Qed.

(* Directly fold sllb from components *)
Lemma sllbseg_store_2_sllb: forall x pt l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
  sllbseg (&(x # "sllb" ->ₛ "head")) pt l **
  pt # Ptr |-> NULL |--
  sllb x l.
Proof.
  intros. unfold sllb. destruct l.
  + simpl sllbseg. Intros. subst pt. entailer!.
  + Exists pt. entailer!.
Qed.

(* For app_list_box: sllbseg + pt |-> h + sll h l2 => sllbseg of l1++l2 *)
Lemma sllbseg_pt_sll: forall x pt l1 h l2,
  sllbseg x pt l1 ** pt # Ptr |-> h ** sll h l2 |--
  EX pt_new: addr, sllbseg x pt_new (l1 ++ l2) ** pt_new # Ptr |-> NULL.
Proof.
  intros.
  sep_apply sllbseg_sll.
  Intros head_val.
  sep_apply (sll_2_sllbseg x head_val (l1 ++ l2)).
  Intros pt_new.
  Exists pt_new.
  entailer!.
Qed.

(* For app_list_box return_wit_1: when h2 = 0 *)
Lemma app_sllb_case_nil: forall x pt l1 l2,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
  sllbseg (&(x # "sllb" ->ₛ "head")) pt l1 **
  pt # Ptr |-> NULL **
  sll NULL l2 |--
  sllb x (l1 ++ l2).
Proof.
  intros.
  assert (Hnil: NULL = NULL) by reflexivity.
  sep_apply (sll_zero NULL l2 Hnil).
  Intros. subst l2.
  rewrite app_nil_r.
  sep_apply (sllbseg_store_2_sllb x pt l1 H).
  entailer!.
Qed.

(* For app_list_box return_wit_2: directly construct sllb using pt2 as final ptail *)
(* Key insight: pt2 from sllb(b2, l2) IS the final ptail because sll(h2, l2)'s 
   tail pointer position is exactly pt2. The sll_2_sllbseg gives the same pt. *)

(* Direct folding into sllb when we have the right structure *)
Lemma app_sllb_direct: forall x pt l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
  sllbseg (&(x # "sllb" ->ₛ "head")) pt l **
  pt # Ptr |-> NULL |--
  sllb x l.
Proof.
  intros. unfold sllb. destruct l.
  + simpl sllbseg. Intros. subst pt. entailer!.
  + Exists pt. entailer!.
Qed.

(* For return_wit_2: Connect l1 and l2 using sll, then fold to sllb *)
(* This uses sllbseg_pt_sll which gives EX pt_final, and we need to use that pt_final *)
Lemma app_sllb_via_sll: forall x pt2 pt1 l1 h2 l2,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt2 **
  sllbseg (&(x # "sllb" ->ₛ "head")) pt1 l1 **
  pt1 # Ptr |-> h2 **
  sll h2 l2 |--
  EX pt_final: addr,
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt2 **
    sllbseg (&(x # "sllb" ->ₛ "head")) pt_final (l1 ++ l2) **
    pt_final # Ptr |-> NULL.
Proof.
  intros.
  sep_apply (sllbseg_pt_sll (&(x # "sllb" ->ₛ "head")) pt1 l1 h2 l2).
  Intros pt_final.
  Exists pt_final.
  entailer!.
Qed.

(* ============================================================ *)
(* New lemmas for app_list_box with split sllb definition *)
(* ============================================================ *)

(* Direct append with sllbseg only - core lemma for app_list_box *)
(* After writing pt1 |-> h2, we can connect l1 and (a::l2) *)
Lemma sllbseg_append_sllbseg: forall x pt1 l1 h2 pt2 a l2,
  h2 <> NULL ->
  sllbseg x pt1 l1 ** 
  pt1 # Ptr |-> h2 ** 
  &(h2 # "sll" ->ₛ "data") # UInt |-> a **
  sllbseg (&(h2 # "sll" ->ₛ "next")) pt2 l2 **
  pt2 # Ptr |-> NULL |--
  sllbseg x pt2 (l1 ++ a :: l2) ** pt2 # Ptr |-> NULL.
Proof.
  intros. revert x. induction l1; simpl; intros.
  + Intros. subst x. Exists h2. entailer!.
  + Intros u. Exists u. sep_apply IHl1. entailer!.
Qed.

(* For app_list_box return_wit_2: when l2 is non-empty *)
(* After executing *pt1 = h2, we have pt1 |-> h2 (not NULL) *)
(* sllbseg for b2's content starts from &(b2->head) |-> h2 *)
Lemma app_sllb_nonempty_direct: forall x pt1 l1 pt2 h2 a l2,
  x <> NULL -> h2 <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt2 **
  sllbseg (&(x # "sllb" ->ₛ "head")) pt1 l1 **
  pt1 # Ptr |-> h2 ** 
  &(h2 # "sll" ->ₛ "data") # UInt |-> a **
  sllbseg (&(h2 # "sll" ->ₛ "next")) pt2 l2 **
  pt2 # Ptr |-> NULL |--
  sllb x (l1 ++ a :: l2).
Proof.
  intros.
  sep_apply (sllbseg_append_sllbseg (&(x # "sllb" ->ₛ "head")) pt1 l1 h2 pt2 a l2 H0).
  sep_apply (sllbseg_store_2_sllb x pt2 (l1 ++ a :: l2) H).
  entailer!.
Qed.
