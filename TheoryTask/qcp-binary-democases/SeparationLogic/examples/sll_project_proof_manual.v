Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import sll_project_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import sll_project_lib.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_cons_list_return_wit_1 : cons_list_return_wit_1.
Proof.
  pre_process.
  simpl sll. Exists next_pre. entailer!.
Qed.

Lemma proof_of_free_list_return_wit_1 : free_list_return_wit_1.
Proof.
  pre_process.
  subst head.
  sep_apply sll_zero.
  - entailer!.
  - entailer!.
Qed.

Lemma proof_of_free_list_which_implies_wit_1 : free_list_which_implies_wit_1.
Proof.
  pre_process.
  destruct l_rest as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros y.
    Exists y a l0. entailer!.
Qed.

Lemma proof_of_map_list_entail_wit_1 : map_list_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) l.
  simpl sllseg. simpl app. simpl map_mult. entailer!.
Qed.

Lemma proof_of_map_list_entail_wit_2 : map_list_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ (p_data :: nil)) l2_new.
  entailer!.
  - sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg.
    assert (H_eq: map_mult x_pre (l1_2 ++ p_data :: nil) = map_mult x_pre l1_2 ++ unsigned_last_nbits (x_pre * p_data) 32 :: nil).
    { unfold map_mult. rewrite map_app. simpl. reflexivity. }
    rewrite H_eq. entailer!.
  - rewrite H1, H. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma proof_of_map_list_return_wit_1 : map_list_return_wit_1.
Proof.
  pre_process.
  subst p.
  sep_apply sll_zero; try tauto.
  Intros. subst l2.
  sep_apply sllseg_0_sll.
  rewrite app_nil_r in H0. subst l. entailer!.
Qed.

Lemma proof_of_map_list_which_implies_wit_1 : map_list_which_implies_wit_1.
Proof.
  pre_process.
  (* p <> 0 and sll p l2, so l2 must be non-empty *)
  destruct l2 as [ | a l0].
  - (* l2 = nil, but p <> 0, contradiction *)
    simpl sll. Intros. tauto.
  - (* l2 = a :: l0 *)
    simpl sll. Intros. Intros y.
    Exists y a l0.
    entailer!.
Qed. 

Lemma proof_of_cons_list_box_return_wit_1 : cons_list_box_return_wit_1.
Proof.
  pre_process.
  (* l = nil from hypothesis, so new list is data_pre :: nil *)
  subst l.
  (* sll retval [data_pre] = retval <> NULL /\ EX y, &(retval->data) |-> data_pre ** &(retval->next) |-> y ** sll y nil *)
  simpl sll.
  Intros next_val.
  simpl sll.
  Intros. subst next_val.
  (* Now we know &(retval->next) |-> NULL *)
  (* Choose pt_new = &(retval->next) which matches store(&(box->ptail), &(retval->next)) *)
  Exists (&(retval # "sll" ->ₛ "next")).
  simpl sllbseg.
  Exists retval.
  simpl sllbseg.
  entailer!.
Qed. 

Lemma proof_of_cons_list_box_return_wit_2 : cons_list_box_return_wit_2.
Proof.
  pre_process.
  (* l <> nil from hypothesis, so original list was non-empty *)
  (* box->ptail stays at pt (not updated) *)
  (* Use sll_2_sllbseg to convert sll to sllbseg *)
  sep_apply (sll_2_sllbseg (&(box_pre # "sllb" ->ₛ "head")) retval (data_pre :: l)).
  Intros pt_new.
  Exists pt_new.
  entailer!.
Qed. 

Lemma proof_of_cons_list_box_which_implies_wit_1 : cons_list_box_which_implies_wit_1.
Proof.
  pre_process.
  (* Use sllbseg_0_sll' to convert sllbseg + store(pt, 0) to store + sll *)
  sep_apply (sllbseg_0_sll' (&(box # "sllb" ->ₛ "head")) pt l).
  Intros h.
  Exists h.
  entailer!.
Qed. 

Lemma proof_of_map_list_box_return_wit_1 : map_list_box_return_wit_1.
Proof.
  pre_process.
  (* Use sll_2_sllbseg to convert sll to sllbseg *)
  sep_apply (sll_2_sllbseg (&(box_pre # "sllb" ->ₛ "head")) h (map_mult x_pre l)).
  Intros pt_new.
  Exists pt_new.
  entailer!.
Qed. 

Lemma proof_of_map_list_box_which_implies_wit_1 : map_list_box_which_implies_wit_1.
Proof.
  pre_process.
  (* Use sllbseg_0_sll' to convert sllbseg + store(pt, 0) to store + sll *)
  sep_apply (sllbseg_0_sll' (&(box # "sllb" ->ₛ "head")) pt l).
  Intros h.
  Exists h.
  entailer!.
Qed. 

Lemma proof_of_app_list_box_return_wit_1 : app_list_box_return_wit_1.
Proof.
  pre_process.
  (* h2 = 0, so l2 = nil by sll_pt definition *)
  unfold sll_pt.
  destruct l2.
  + (* l2 = nil *)
    Intros. subst h2.
    rewrite app_nil_r.
    (* Now: &(b1->ptail) |-> pt1 ** sllbseg(&(b1->head), pt1, l1) ** pt1 |-> 0 *)
    sep_apply (sllbseg_store_2_sllb b1_pre pt1 l1).
    entailer!.
    rewrite <- H2.
    tauto.
  + (* l2 = z :: l2, but h2 = 0 contradicts h2 <> NULL *)
    Intros. tauto.
Qed.

Lemma proof_of_app_list_box_return_wit_2 : app_list_box_return_wit_2.
Proof.
  pre_process.
  (* h2 <> 0, so l2 = a :: l2' for some a, l2' *)
  unfold sll_pt.
  destruct l2.
  + (* l2 = nil implies h2 = NULL, contradiction *)
    Intros. tauto.
  + (* l2 = z :: l2 *)
    Intros.
    (* Now have:
       &(b1->ptail) |-> pt2 **
       sllbseg(&(b1->head), pt1, l1) **
       pt1 |-> h2 **
       &(h2->data) |-> z **
       sllbseg(&(h2->next), pt2, l2) **
       pt2 |-> NULL *)
    sep_apply (sllbseg_append_sllbseg (&(b1_pre # "sllb" ->ₛ "head")) pt1 l1 h2 pt2 z l2 H).
    sep_apply (sllbseg_store_2_sllb b1_pre pt2 (l1 ++ z :: l2) H0).
    entailer!.
Qed.

Lemma proof_of_app_list_box_which_implies_wit_1 : app_list_box_which_implies_wit_1.
Proof.
  pre_process.
  (* Use the key lemma we proved in lib *)
  sep_apply (app_list_box_which_implies_valid b1 b2 l1 l2).
  Intros pt1 h2 pt2.
  Exists pt2 h2 pt1.
  entailer!.
Qed. 

Lemma proof_of_sll_length_entail_wit_1 : sll_length_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) l.
  simpl sllseg. simpl app. simpl Zlength. entailer!.
Qed.

Lemma proof_of_sll_length_entail_wit_2 : sll_length_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ (head_data :: nil)) l3.
  simpl.
  entailer!.
  sep_apply sllseg_len1.
  - rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg. entailer!.
  - entailer!.
  - rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil.
    rewrite <- H2.
    apply unsigned_last_nbits_eq.
    rewrite H1, H in H3.
    rewrite Zlength_app, Zlength_cons in H3.
    pose proof (Zlength_nonneg l1_2).
    rewrite <- H2 in H4.
    pose proof (Zlength_nonneg l3). lia.
  - rewrite H1, H. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma proof_of_sll_length_return_wit_1 : sll_length_return_wit_1.
Proof.
  pre_process.
  rewrite H.
  sep_apply sll_zero.
  subst l.
  entailer!.
  - rewrite H0, app_nil_r. sep_apply sllseg_0_sll. entailer!.
  - rewrite H0, app_nil_r. assumption.
  - reflexivity.
Qed.

Lemma proof_of_sll_length_which_implies_wit_1 : sll_length_which_implies_wit_1.
Proof.
  pre_process.
  destruct l2 as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros x.
    Exists x a l0. entailer!.
Qed. 

Lemma proof_of_sll2array_entail_wit_1 : sll2array_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) l.
  simpl sllseg. simpl Zlength. simpl app.
  rewrite (UIntArray.ceil_shape_empty retval_2 0).
  entailer!.
  rewrite H.
  pose proof (Zlength_nonneg l).
  lia.
Qed.

Lemma proof_of_sll2array_entail_wit_2 : sll2array_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ p_data :: nil) l3.
  entailer!.
  - (* Separation logic goal: sllseg + ceil_shape *)
    (* First handle ceil_shape extension *)
    sep_apply (UIntArray.ceil_shape_single arr i p_data).
    sep_apply (UIntArray.ceil_shape_merge_to_ceil_shape arr 0 i (i+1)); try lia.
    (* Now handle sllseg extension *)
    sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg.
    entailer!.
  - (* Zlength part *)
    rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - (* app part *)
    rewrite H2, H. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma proof_of_sll2array_return_wit_1 : sll2array_return_wit_1.
Proof.
  pre_process.
  subst p.
  sep_apply sll_zero; try tauto.
  Intros. subst l2.
  rewrite app_nil_r in H0.
  subst l.
  Exists arr.
  sep_apply sllseg_0_sll.
  (* Now need: ceil_shape arr 0 i ** undef_ceil arr i len |-- full_shape arr len *)
  (* When i = len = Zlength l1 (since l1 = l and l2 = nil), undef_ceil is empty *)
  (* First, unify all indices using H1 and H2 *)
  rewrite H1. (* Replace i with Zlength l1 *)
  rewrite H2. (* Replace len with Zlength l1 *)
  rewrite (UIntArray.undef_ceil_empty arr (Zlength l1)).
  sep_apply (UIntArray.ceil_shape_to_full_shape arr 0 (Zlength l1)).
  replace (arr + 0 * sizeof(UINT)) with arr by lia.
  replace (Zlength l1 - 0) with (Zlength l1) by lia.
  entailer!.
Qed.

Lemma proof_of_sll2array_partial_solve_wit_3_pure : sll2array_partial_solve_wit_3_pure.
Proof.
  pre_process.
  (* Need to show: l = app l1 l2 /\ p <> 0 /\ i < len *)
  (* From hypothesis, we have p <> 0 and sll p l2 *)
  (* sll p l2 with p <> 0 implies l2 is non-empty, hence Zlength l2 >= 1 *)
  (* So i = Zlength l1 < Zlength l1 + Zlength l2 = Zlength (l1 ++ l2) = Zlength l = len *)
  prop_apply (sll_not_null_length p l2 H).
  Intros.
  entailer!.
  (* Goal: i < len *)
  (* Use H1: i = Zlength l1, H2: len = Zlength l, H0: l = l1 ++ l2 *)
  subst i len.
  rewrite H0.
  rewrite Zlength_app.
  (* Now goal is: Zlength l1 < Zlength l1 + Zlength l2, and we have H7: Zlength l2 >= 1 *)
  lia.
Qed.

Lemma proof_of_sll2array_which_implies_wit_1 : sll2array_which_implies_wit_1.
Proof.
  pre_process.
  destruct l2 as [ | a l0].
  - (* l2 = nil, but p <> 0, contradiction *)
    simpl sll. Intros. tauto.
  - (* l2 = a :: l0 *)
    simpl sll. Intros. Intros y.
    Exists y a l0.
    entailer!.
Qed.

Lemma proof_of_sllb2array_return_wit_1 : sllb2array_return_wit_1.
Proof.
  pre_process.
  (* Use sll_2_sllbseg to convert sll to sllbseg *)
  sep_apply (sll_2_sllbseg (&(box_pre # "sllb" ->ₛ "head")) h l).
  Intros pt_new.
  Exists arr_ret_2 pt_new.
  entailer!.
Qed. 

Lemma proof_of_sllb2array_which_implies_wit_1 : sllb2array_which_implies_wit_1.
Proof.
  pre_process.
  (* Use sllbseg_0_sll' to convert sllbseg + store(pt, 0) to store + sll *)
  sep_apply (sllbseg_0_sll' (&(box # "sllb" ->ₛ "head")) pt l).
  Intros h.
  Exists h.
  entailer!.
Qed. 

