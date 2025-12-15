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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function chars_initialize -----*)

Definition chars_initialize_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Char  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.undef_full a_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition chars_initialize_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full a_pre (i + 1 ) (app ((repeat_Z (m_pre) (i))) ((cons (m_pre) (nil)))) )
  **  (CharArray.undef_ceil a_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Char  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition chars_initialize_entail_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.undef_full a_pre n_pre )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full a_pre 0 (repeat_Z (m_pre) (0)) )
  **  (CharArray.undef_ceil a_pre 0 n_pre )
.

Definition chars_initialize_entail_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full a_pre (i + 1 ) (app ((repeat_Z (m_pre) (i))) ((cons (m_pre) (nil)))) )
  **  (CharArray.undef_ceil a_pre (i + 1 ) n_pre )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full a_pre (i + 1 ) (repeat_Z (m_pre) ((i + 1 ))) )
  **  (CharArray.undef_ceil a_pre (i + 1 ) n_pre )
.

Definition chars_initialize_return_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
  **  (CharArray.undef_ceil a_pre i n_pre )
|--
  (CharArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)) )
.

Definition chars_initialize_partial_solve_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
  **  (CharArray.undef_ceil a_pre i n_pre )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i a_pre i i n_pre )
  **  (CharArray.full a_pre i (repeat_Z (m_pre) (i)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_chars_initialize_safety_wit_1 : chars_initialize_safety_wit_1.
Axiom proof_of_chars_initialize_safety_wit_2 : chars_initialize_safety_wit_2.
Axiom proof_of_chars_initialize_entail_wit_1 : chars_initialize_entail_wit_1.
Axiom proof_of_chars_initialize_entail_wit_2 : chars_initialize_entail_wit_2.
Axiom proof_of_chars_initialize_return_wit_1 : chars_initialize_return_wit_1.
Axiom proof_of_chars_initialize_partial_solve_wit_1 : chars_initialize_partial_solve_wit_1.

End VC_Correct.
