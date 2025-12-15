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
From SimpleC.EE Require Import chars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_chars_initialize_entail_wit_1 : chars_initialize_entail_wit_1.
Proof.
  pre_process. 
  entailer!. 
  unfold repeat_Z. simpl. 
  sep_apply CharArray.undef_full_to_undef_ceil.
  entailer!.
  cbn.
  entailer!. 
Qed. 

Lemma proof_of_chars_initialize_entail_wit_2 : chars_initialize_entail_wit_2.
Proof.
  pre_process. 
  entailer!.
  rewrite repeat_Z_tail ; try lia. 
  entailer!.
Qed.

Lemma proof_of_chars_initialize_return_wit_1 : chars_initialize_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia. 
  subst.
  rewrite (CharArray.undef_ceil_empty a_pre n_pre).
  entailer!.
Qed.

