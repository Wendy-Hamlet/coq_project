Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import avl_strategy_goal.
Require Import avl_shape.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma avl_strategy0_correctness : avl_strategy0.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma avl_strategy9_correctness : avl_strategy9.
  pre_process_default.
Qed.

Lemma avl_strategy12_correctness : avl_strategy12.
  pre_process_default.
Qed.

Lemma avl_strategy7_correctness : avl_strategy7.
  pre_process_default.
  unfold single_tree_node.
  entailer!.
Qed.

Lemma avl_strategy8_correctness : avl_strategy8.
  pre_process_default.
  unfold single_tree_node.
  entailer!.
Qed.

Lemma avl_strategy1_correctness : avl_strategy1.
  pre_process_default.
  unfold store_tree at 1.
  destruct tr.
  - entailer!.
  - Intros pl pr k v h.
    Exists k v h pl pr.
    Exists tr1 tr2.
    unfold single_tree_node.
    unfold store_tree.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
Qed.

Lemma avl_strategy2_correctness : avl_strategy2.
  pre_process.
  entailer!.
  Intros_r tr.
  Intros_r tr1.
  Intros_r tr2.
  Intros_r k.
  Intros_r v.
  Intros_r h.
  Intros_r k0.
  Intros_r r.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  unfold store_tree at 3.
  subst tr.
  Exists k r k0 v h.
  unfold single_tree_node.
  entailer!.
Qed.

Lemma avl_strategy3_correctness : avl_strategy3.
  pre_process_default.
  subst p.
  unfold store_tree.
  destruct tr eqn:Htr.
  - entailer!.
  - Intros pl pr k v h.
    exfalso.
    apply H.
    reflexivity.
Qed.

Lemma avl_strategy4_correctness : avl_strategy4.
  pre_process_default.
  entailer!.
  Intros_r tr.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst tr.
  unfold store_tree.
  entailer!.
Qed.

Lemma avl_strategy10_correctness : avl_strategy10.
  pre_process_default.
  unfold store_tree_shape.
  Intros tr.
  Exists tr.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma avl_strategy11_correctness : avl_strategy11.
  pre_process_default.
  unfold store_tree_shape.
  Exists tr.
  entailer!.
Qed.

Lemma avl_strategy13_correctness : avl_strategy13.
  pre_process_default.
  unfold store_non_empty_tree.
  entailer!.
Qed.

Lemma avl_strategy15_correctness : avl_strategy15.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  unfold store_non_empty_tree.
  entailer!.
Qed.

Lemma avl_strategy16_correctness : avl_strategy16.
  pre_process_default.
  entailer!.
  Intros_r tr.
  Intros_r tr1.
  Intros_r tr2.
  Intros_r l.
  Intros_r v.
  Intros_r h.
  Intros_r k.
  Intros_r r.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst tr.
  unfold store_tree at 3.
  Exists l r k v h.
  unfold single_tree_node.
  entailer!.
Qed.

Lemma avl_strategy17_correctness : avl_strategy17.
  pre_process.
  entailer!.
  subst tr.
  unfold store_tree.
  entailer!.
Qed.

Lemma avl_strategy5_correctness : avl_strategy5.
  pre_process_default.
  unfold single_tree_node.
  entailer!.
Qed.

Lemma avl_strategy6_correctness : avl_strategy6.
  pre_process_default.
  unfold single_tree_node.
  entailer!.
Qed.

Lemma avl_strategy25_correctness : avl_strategy25.
  pre_process_default.
  prop_apply (valid_store_uchar p). entailer!.
Qed.

Lemma avl_strategy26_correctness : avl_strategy26.
  pre_process_default.
  prop_apply (valid_store_uchar p). entailer!.
Qed.