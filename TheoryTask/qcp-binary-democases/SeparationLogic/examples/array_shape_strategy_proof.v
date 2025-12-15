Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import array_shape_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma array_shape_strategy1_correctness : array_shape_strategy1.
  pre_process_default.
  sep_apply UIntArray.full_shape_split_to_missing_i_shape ; eauto.
  Intros a.
  Exists a.
  entailer!.
  Intros_r v.
  pre_process_default.
Qed.

Lemma array_shape_strategy3_correctness : array_shape_strategy3.
  pre_process_default.
  sep_apply (UIntArray.ceil_shape_split_to_ceil_shape p x (x + 1) y) ; try lia.
  rewrite (UIntArray.ceil_shape_unfold p x (x + 1)) ; try lia.
  Intros a. Exists a.
  rewrite (UIntArray.ceil_shape_empty).
  entailer!.
  Intros_r v.
  pre_process_default.
Qed.

Lemma array_shape_strategy6_correctness : array_shape_strategy6.
  pre_process_default.
  subst.
  rewrite (UIntArray.ceil_shape_empty).
  entailer!.
Qed.

Lemma array_shape_strategy7_correctness : array_shape_strategy7.
  pre_process_default.
  subst.
  rewrite (UIntArray.ceil_shape_empty).
  entailer!.
Qed.

Lemma array_shape_strategy8_correctness : array_shape_strategy8.
  pre_process_default.
  subst.
  rewrite (UIntArray.full_shape_empty).
  entailer!.
Qed.

Lemma array_shape_strategy9_correctness : array_shape_strategy9.
  pre_process_default.
  subst i.
  sep_apply (UIntArray.ceil_shape_to_full_shape).
  replace (p + 0 * sizeof ( UINT )) with p by lia.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma array_shape_strategy10_correctness : array_shape_strategy10.
  pre_process_default.
  subst y1.
  entailer!.
Qed.

Lemma array_shape_strategy11_correctness : array_shape_strategy11.
  pre_process_default.
  sep_apply IntArray.full_shape_split_to_missing_i_shape ; eauto.
  Intros a.
  Exists a.
  entailer!.
  Intros_r v.
  pre_process_default.
Qed.

Lemma array_shape_strategy13_correctness : array_shape_strategy13.
  pre_process_default.
  sep_apply (IntArray.ceil_shape_split_to_ceil_shape p x (x + 1) y) ; try lia.
  rewrite (IntArray.ceil_shape_unfold p x (x + 1)) ; try lia.
  Intros a. Exists a.
  rewrite (IntArray.ceil_shape_empty).
  entailer!.
  Intros_r v.
  pre_process_default.
Qed.

Lemma array_shape_strategy16_correctness : array_shape_strategy16.
  pre_process_default.
  subst.
  rewrite (IntArray.ceil_shape_empty).
  entailer!.
Qed.

Lemma array_shape_strategy17_correctness : array_shape_strategy17.
  pre_process_default.
  subst.
  rewrite (IntArray.ceil_shape_empty).
  entailer!.
Qed.

Lemma array_shape_strategy18_correctness : array_shape_strategy18.
  pre_process_default.
  subst.
  rewrite (IntArray.full_shape_empty).
  entailer!.
Qed.

Lemma array_shape_strategy19_correctness : array_shape_strategy19.
  pre_process_default.
  subst i.
  sep_apply (IntArray.ceil_shape_to_full_shape).
  replace (p + 0 * sizeof ( INT )) with p by lia.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma array_shape_strategy20_correctness : array_shape_strategy20.
  pre_process_default.
  subst y1.
  entailer!.
Qed.

Lemma array_shape_strategy2_correctness : array_shape_strategy2.
  pre_process_default.
  sep_apply (UIntArray.missing_i_shape_merge_to_full_shape p i n v) ; try lia.
  entailer!.
Qed.

Lemma array_shape_strategy4_correctness : array_shape_strategy4.
  pre_process_default.
  sep_apply UIntArray.ceil_single.
  sep_apply UIntArray.ceil_to_ceil_shape.
  subst x.
  prop_apply (UIntArray.ceil_shape_valid p (i + 1) y). Intros.
  sep_apply (UIntArray.ceil_shape_merge_to_ceil_shape p i (i + 1) y); try lia.
  entailer!.
Qed.

Lemma array_shape_strategy5_correctness : array_shape_strategy5.
  pre_process_default.
  sep_apply UIntArray.ceil_single.
  sep_apply UIntArray.ceil_to_ceil_shape.
  prop_apply (UIntArray.ceil_shape_valid p y z). Intros.
  sep_apply (UIntArray.ceil_shape_merge_to_ceil_shape p y z (z + 1)); try lia.
  entailer!.
Qed.

Lemma array_shape_strategy12_correctness : array_shape_strategy12.
  pre_process_default.
  sep_apply (IntArray.missing_i_shape_merge_to_full_shape p i n v) ; try lia.
  entailer!.
Qed.

Lemma array_shape_strategy14_correctness : array_shape_strategy14.
  pre_process_default.
  sep_apply IntArray.ceil_single.
  sep_apply IntArray.ceil_to_ceil_shape.
  subst x.
  prop_apply (IntArray.ceil_shape_valid p (i + 1) y). Intros.
  sep_apply (IntArray.ceil_shape_merge_to_ceil_shape p i (i + 1) y); try lia.
  entailer!.
Qed.

Lemma array_shape_strategy15_correctness : array_shape_strategy15.
  pre_process_default.
  sep_apply IntArray.ceil_single.
  sep_apply IntArray.ceil_to_ceil_shape.
  prop_apply (IntArray.ceil_shape_valid p y z). Intros.
  sep_apply (IntArray.ceil_shape_merge_to_ceil_shape p y z (z + 1)); try lia.
  entailer!.
Qed.
