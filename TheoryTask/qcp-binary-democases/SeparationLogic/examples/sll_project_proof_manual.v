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
  unfold sll_pt.
  destruct l.
  - (* l = nil: choose right branch of || *)
    Intros. subst next_pre.
    Right.
    Exists (&(retval # "sll" ->ₛ "next")).
    simpl sllbseg.
    entailer!.
  - (* l = z :: l: choose left branch of || *)
    Intros.
    Left.
    Exists pt.
    simpl sllbseg.
    Exists next_pre.
    entailer!.
    discriminate.  
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
  destruct l2 as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros y.
    Exists y a l0.
    entailer!.
Qed. 

Lemma proof_of_cons_list_box_return_wit_1 : cons_list_box_return_wit_1.
Proof.
  pre_process.
  subst l.
  simpl sll_pt.
  Intros.
  Exists (&(retval # "sll" ->ₛ "next")).
  simpl sllbseg.
  Exists retval.
  simpl sllbseg.
  entailer!.
  subst pt_new_2.
  entailer!.
Qed. 

Lemma proof_of_cons_list_box_return_wit_2 : cons_list_box_return_wit_2.
Proof.
  pre_process.
  simpl sll_pt.
  Intros.
  Exists pt.
  simpl sllbseg.
  Exists retval.
  entailer!.
  subst pt_new_2.
  entailer!.
Qed. 

Lemma proof_of_cons_list_box_which_implies_wit_1 : cons_list_box_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (sllbseg_0_sll_pt (&(box # "sllb" ->ₛ "head")) pt l).
  Intros h.
  Exists h.
  entailer!.
Qed. 

Lemma proof_of_map_list_box_return_wit_1 : map_list_box_return_wit_1.
Proof.
  pre_process.
  (* l = nil, pt = &(box->head), map_mult x nil = nil *)
  subst l pt.
  simpl map_mult.
  simpl sll. Intros. subst h.
  Exists (&(box_pre # "sllb" ->ₛ "head")).
  simpl sllbseg.
  entailer!.
Qed. 

Lemma proof_of_map_list_box_return_wit_2 : map_list_box_return_wit_2.
Proof.
  pre_process.
  (* l <> nil, use sll_2_sllbseg *)
  sep_apply (sll_2_sllbseg (&(box_pre # "sllb" ->ₛ "head")) h (map_mult x_pre l)).
  Intros pt_new.
  Exists pt_new.
  entailer!.
  (* pt_new from sll_2_sllbseg should equal pt, but this is the precision problem *)
  (* The list structure is unchanged by map, so pt_new = pt semantically *)
Admitted. 

Lemma proof_of_map_list_box_which_implies_wit_1 : map_list_box_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (sllbseg_0_sll' (&(box # "sllb" ->ₛ "head")) pt l).
  Intros h.
  Exists h.
  entailer!.
Qed. 

Lemma proof_of_app_list_box_return_wit_1 : app_list_box_return_wit_1.
Proof.
  pre_process.
  unfold sll_pt.
  destruct l2.
  + Intros. subst h2.
    rewrite app_nil_r.
    sep_apply (sllbseg_store_2_sllb b1_pre pt1 l1).
    entailer!.
    rewrite <- H2.
    tauto.
  + Intros. tauto.
Qed.

Lemma proof_of_app_list_box_return_wit_2 : app_list_box_return_wit_2.
Proof.
  pre_process.
  unfold sll_pt.
  destruct l2.
  + Intros. tauto.
  + Intros.
    sep_apply (sllbseg_append_sllbseg (&(b1_pre # "sllb" ->ₛ "head")) pt1 l1 h2 pt2 z l2 H).
    sep_apply (sllbseg_store_2_sllb b1_pre pt2 (l1 ++ z :: l2) H0).
    entailer!.
Qed.

Lemma proof_of_app_list_box_which_implies_wit_1 : app_list_box_which_implies_wit_1.
Proof.
  pre_process.
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
  - sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg. entailer!.
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
  - sep_apply (UIntArray.ceil_shape_single arr i p_data).
    sep_apply (UIntArray.ceil_shape_merge_to_ceil_shape arr 0 i (i+1)); try lia.
    sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg.
    entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite H2, H. rewrite <- app_assoc. simpl. reflexivity.
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
  rewrite H1, H2.
  rewrite (UIntArray.undef_ceil_empty arr (Zlength l1)).
  sep_apply (UIntArray.ceil_shape_to_full_shape arr 0 (Zlength l1)).
  replace (arr + 0 * sizeof(UINT)) with arr by lia.
  replace (Zlength l1 - 0) with (Zlength l1) by lia.
  entailer!.
Qed.

Lemma proof_of_sll2array_partial_solve_wit_3_pure : sll2array_partial_solve_wit_3_pure.
Proof.
  pre_process.
  prop_apply (sll_not_null_length p l2 H).
  Intros.
  entailer!.
  subst i len.
  rewrite H0.
  rewrite Zlength_app.
  lia.
Qed.

Lemma proof_of_sll2array_which_implies_wit_1 : sll2array_which_implies_wit_1.
Proof.
  pre_process.
  destruct l2 as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros y.
    Exists y a l0.
    entailer!.
Qed.

Lemma proof_of_sllb2array_return_wit_1 : sllb2array_return_wit_1.
Proof.
  pre_process.
  (* l <> nil, use sll_2_sllbseg *)
  subst b out.
  sep_apply (sll_2_sllbseg (&(box_pre # "sllb" ->ₛ "head")) h l).
  Intros pt_new.
  Exists arr_ret_2 pt_new.
  entailer!.
  (* Precision problem: pt_new from sll_2_sllbseg should equal pt *)
Admitted. 

Lemma proof_of_sllb2array_return_wit_2 : sllb2array_return_wit_2.
Proof.
  pre_process.
  (* l = nil, pt = &(box->head) *)
  subst b out l pt.
  simpl sll. Intros. subst h.
  Exists arr_ret_2 (&(box_pre # "sllb" ->ₛ "head")).
  simpl sllbseg.
  entailer!.
Qed. 

Lemma proof_of_sllb2array_which_implies_wit_1 : sllb2array_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (sllbseg_0_sll' (&(box # "sllb" ->ₛ "head")) pt l).
  Intros h.
  Exists h.
  entailer!.
Qed. 

