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
  sep_apply (sll_zero NULL l_rest).
  { reflexivity. }
  Intros. subst l_rest. entailer!.
Qed.

Lemma proof_of_free_list_which_implies_wit_1 : free_list_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (sll_not_zero head l_rest H).
  Intros y a l0.
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
  Exists (l1_2 ++ [p_data]) l2_new.
  rewrite map_mult_cons.
  sep_apply (sllseg_sllseg head_pre p p_next (map_mult x_pre l1_2) [unsigned_last_nbits (x_pre * p_data) 32]).
  simpl sllseg. Exists p_next.
  entailer!.
  subst l2_2. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma proof_of_map_list_return_wit_1 : map_list_return_wit_1.
Proof.
  pre_process.
  subst p.
  sep_apply (sll_zero NULL l2).
  { reflexivity. }
  Intros. subst l2.
  rewrite app_nil_r.
  sep_apply (sllseg_0_sll head_pre (map_mult x_pre l1)).
  entailer!.
Qed.

Lemma proof_of_map_list_which_implies_wit_1 : map_list_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (sll_not_zero p l2 H0).
  Intros y a l0.
  Exists y a l0. entailer!.
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
  Exists (l1_2 ++ [head_data]) l3.
  sep_apply (sllseg_sllseg head_pre head head_next l1_2 [head_data]).
  simpl sllseg. Exists head_next.
  entailer!.
  + subst l2_2. rewrite <- app_assoc. simpl. reflexivity.
  + rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil.
    subst len. rewrite Z.add_comm.
    pose proof (Zlength_nonneg l1_2).
    assert (Hbound: Zlength l1_2 + 1 <= INT_MAX).
    { subst l. rewrite Zlength_app. subst l2_2. rewrite Zlength_cons.
      pose proof (Zlength_nonneg l3). lia. }
    rewrite unsigned_last_nbits_eq; lia.
Qed.

Lemma proof_of_sll_length_return_wit_1 : sll_length_return_wit_1.
Proof.
  pre_process.
  subst head.
  sep_apply (sll_zero NULL l2).
  { reflexivity. }
  Intros. subst l2.
  rewrite app_nil_r.
  sep_apply (sllseg_0_sll head_pre l1).
  entailer!.
Qed.

Lemma proof_of_sll_length_which_implies_wit_1 : sll_length_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (sll_not_zero head l2 H).
  Intros y a l0.
  Exists y a l0. entailer!.
Qed. 

Lemma proof_of_sll2array_entail_wit_1 : sll2array_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_sll2array_entail_wit_2 : sll2array_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_sll2array_return_wit_1 : sll2array_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sll2array_partial_solve_wit_3_pure : sll2array_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_sll2array_which_implies_wit_1 : sll2array_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_sllb2array_return_wit_1 : sllb2array_return_wit_1.
Proof. Admitted. 

