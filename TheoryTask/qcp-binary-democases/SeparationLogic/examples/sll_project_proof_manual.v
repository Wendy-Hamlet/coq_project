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
Import naive_C_Rules.
Require Import sll_project_lib.
Local Open Scope sac.

Lemma proof_of_cons_list_return_wit_1 : cons_list_return_wit_1.
Proof.
  pre_process.
  simpl sll.
  Exists next_pre.
  entailer!.
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
  - (* l_rest = nil, sll head nil means head = 0, contradicts H : head <> 0 *)
    simpl sll.
    Intros.
    (* Now we have head = 0 from sll, but H says head <> 0 *)
    tauto.
  - (* l_rest = a :: l0 *)
    simpl sll.
    Intros.
    Intros y.
    Exists y a l0.
    entailer!.
Qed.

Lemma proof_of_map_list_entail_wit_1 : map_list_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_map_list_entail_wit_2 : map_list_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ (p_data :: nil)) l2_new.
  entailer!.
  - sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg.
    assert (H_eq: map_mult x (l1_2 ++ p_data :: nil) = map_mult x l1_2 ++ unsigned_last_nbits (x * p_data) 32 :: nil).
    {
      unfold map_mult.
      rewrite map_app.
      simpl.
      reflexivity.
    }
    rewrite H_eq.
    entailer!.
  - rewrite H1, H.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_map_list_return_wit_1 : map_list_return_wit_1.
Proof.
  (* Missing loop invariant: head = head_pre && x = x_pre *)
  Admitted. 

Lemma proof_of_map_list_which_implies_wit_1 : map_list_which_implies_wit_1.
Proof.
  pre_process.
  destruct l2 as [ | a l0].
  - simpl sll.
    Intros.
    tauto.
  - simpl sll.
    Intros.
    Intros y.
    Exists y a l0.
    entailer!.
Qed.

Lemma proof_of_nil_list_box_which_implies_wit_1 : nil_list_box_which_implies_wit_1.
Proof.
  pre_process.
  subst box_head box_ptail.
  sep_apply sll_zero.
  rewrite H.
  sep_apply sllb_len1; try tauto.
  - entailer!. 
Admitted.
(* Missing precondition: box != 0 in the C code annotation *)
Lemma proof_of_cons_list_box_return_wit_1 : cons_list_box_return_wit_1.
Proof.
  (* pre_process.
  subst pt.
  simpl sll.
  Intros.
  Intros next.
  sep_apply (sll_2_sllb box_pre retval (data_pre :: l)).
  - tauto.
  - simpl sll. Exists next. entailer!. *)
   (* Missing precondition: box_pre <> NULL *)
Admitted.

Lemma proof_of_cons_list_box_return_wit_2 : cons_list_box_return_wit_2.
Proof.
  (* pre_process.
  simpl sll.
  Intros.
  Intros next.
  sep_apply (sll_2_sllb box_pre retval (data_pre :: l)).
  - tauto.
  - simpl sll. Exists next. entailer!.
  *)
  (* Missing precondition: box_pre <> NULL *)
Admitted.

Lemma proof_of_map_list_box_return_wit_1 : map_list_box_return_wit_1.
Proof. Admitted. 

Lemma proof_of_app_list_box_return_wit_1 : app_list_box_return_wit_1.
Proof. Admitted. 

Lemma proof_of_app_list_box_return_wit_2 : app_list_box_return_wit_2.
Proof. Admitted. 

Lemma proof_of_app_list_box_which_implies_wit_1 : app_list_box_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_length_entail_wit_1 : sll_length_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_length_entail_wit_2 : sll_length_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_sll_length_return_wit_1 : sll_length_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_length_which_implies_wit_1 : sll_length_which_implies_wit_1.
Proof. Admitted. 

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

