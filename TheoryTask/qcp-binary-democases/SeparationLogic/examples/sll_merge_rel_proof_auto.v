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
From SimpleC.EE Require Import sll_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

Lemma proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_safety_wit_3 : merge_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_1_pure : merge_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_2_pure : merge_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_3 : merge_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_4 : merge_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_merge_which_implies_wit_1 : merge_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_which_implies_wit_2 : merge_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_split_rec_safety_wit_1_low_level_spec : split_rec_safety_wit_1_low_level_spec.
Proof. Admitted. 

Lemma proof_of_split_rec_partial_solve_wit_1_low_level_spec_pure : split_rec_partial_solve_wit_1_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_split_rec_partial_solve_wit_1_low_level_spec : split_rec_partial_solve_wit_1_low_level_spec.
Proof. Admitted. 

Lemma proof_of_split_rec_partial_solve_wit_2_low_level_spec_pure : split_rec_partial_solve_wit_2_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_split_rec_partial_solve_wit_2_low_level_spec : split_rec_partial_solve_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_split_rec_partial_solve_wit_3_low_level_spec_pure : split_rec_partial_solve_wit_3_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_split_rec_partial_solve_wit_3_low_level_spec : split_rec_partial_solve_wit_3_low_level_spec.
Proof. Admitted. 

Lemma proof_of_split_rec_which_implies_wit_1 : split_rec_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort_safety_wit_1_low_level_spec : merge_sort_safety_wit_1_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_safety_wit_2_low_level_spec : merge_sort_safety_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_safety_wit_3_low_level_spec : merge_sort_safety_wit_3_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_return_wit_2_low_level_spec : merge_sort_return_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_1_low_level_spec_pure : merge_sort_partial_solve_wit_1_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_1_low_level_spec : merge_sort_partial_solve_wit_1_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_2_low_level_spec_pure : merge_sort_partial_solve_wit_2_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_2_low_level_spec : merge_sort_partial_solve_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_3_low_level_spec : merge_sort_partial_solve_wit_3_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_4_low_level_spec_pure : merge_sort_partial_solve_wit_4_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_4_low_level_spec : merge_sort_partial_solve_wit_4_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_5_low_level_spec_pure : merge_sort_partial_solve_wit_5_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_5_low_level_spec : merge_sort_partial_solve_wit_5_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_6_low_level_spec_pure : merge_sort_partial_solve_wit_6_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_6_low_level_spec : merge_sort_partial_solve_wit_6_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_which_implies_wit_1 : merge_sort_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort_which_implies_wit_2 : merge_sort_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_sort3_safety_wit_1_low_level_spec : merge_sort3_safety_wit_1_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_safety_wit_2_low_level_spec : merge_sort3_safety_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_safety_wit_3_low_level_spec : merge_sort3_safety_wit_3_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_return_wit_2_low_level_spec : merge_sort3_return_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_1_low_level_spec_pure : merge_sort3_partial_solve_wit_1_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_1_low_level_spec : merge_sort3_partial_solve_wit_1_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_2_low_level_spec : merge_sort3_partial_solve_wit_2_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_3_low_level_spec_pure : merge_sort3_partial_solve_wit_3_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_3_low_level_spec : merge_sort3_partial_solve_wit_3_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_4_low_level_spec_pure : merge_sort3_partial_solve_wit_4_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_4_low_level_spec : merge_sort3_partial_solve_wit_4_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_5_low_level_spec : merge_sort3_partial_solve_wit_5_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_6_low_level_spec : merge_sort3_partial_solve_wit_6_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_7_low_level_spec_pure : merge_sort3_partial_solve_wit_7_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_7_low_level_spec : merge_sort3_partial_solve_wit_7_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_8_low_level_spec_pure : merge_sort3_partial_solve_wit_8_low_level_spec_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_8_low_level_spec : merge_sort3_partial_solve_wit_8_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_which_implies_wit_1 : merge_sort3_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort3_which_implies_wit_2 : merge_sort3_which_implies_wit_2.
Proof. Admitted. 

