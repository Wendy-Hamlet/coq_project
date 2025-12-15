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
Require Import kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.
From SimpleC.EE Require Import safeexecE_strategy_goal.
From SimpleC.EE Require Import safeexecE_strategy_proof.

(*----- Function inner -----*)

Definition inner_safety_wit_1_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition inner_safety_wit_2_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) = ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition inner_safety_wit_3_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) = ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition inner_safety_wit_4_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition inner_safety_wit_5_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (j = 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition inner_safety_wit_6_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition inner_safety_wit_7_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition inner_entail_wit_1_low_level_spec := 
forall (j_pre: Z) (ch_pre: Z) (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch_pre) (j_pre)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch_pre) (j_pre)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_entail_wit_2_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_entail_wit_3_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
|--
  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) ((Znth (j - 1 ) vnext0_low_level_spec 0))) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_return_wit_1_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) = ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (safeExec ATrue (return ((j + 1 ))) X_low_level_spec ) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) < (m_low_level_spec + 1 )) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_return_wit_2_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (j = 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (safeExec ATrue (return (0)) X_low_level_spec ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < (m_low_level_spec + 1 )) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_partial_solve_wit_1_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (((str_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre j 0 (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_partial_solve_wit_2_low_level_spec := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0_low_level_spec) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (((vnext_pre + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) vnext0_low_level_spec 0))
  **  (IntArray.missing_i vnext_pre (j - 1 ) 0 m_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
.

(*----- Function constr -----*)

Definition constr_safety_wit_1_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (IntArray.full retval_2 retval l )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition constr_safety_wit_2_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (IntArray.full retval_2 retval l )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition constr_safety_wit_3_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full retval_2 retval (replace_Znth (0) (0) (l)) )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition constr_safety_wit_4_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  (IntArray.full retval_2 retval (replace_Znth (0) (0) (l)) )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition constr_safety_wit_5_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) ,
  [| (l0 = (cons (a) (l1))) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((vnext + (i * sizeof(INT) ) )) # Int  |-> retval)
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT) ) ) (n_low_level_spec - (i + 1 ) ) l1 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition constr_entail_wit_1_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval_2: Z) (l: (@list Z)) (retval: Z) ,
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (IntArray.full retval retval_2 (replace_Znth (0) (0) (l)) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval_2)
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (1) (vnext0) (0)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= 1) |]
  &&  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full retval 1 vnext0 )
  **  (IntArray.full (retval + (1 * sizeof(INT) ) ) (n_low_level_spec - 1 ) l0 )
.

Definition constr_entail_wit_2_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0_2: (@list Z)) (vnext: Z) (i: Z) (vnext0_2: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) ,
  [| (l0_2 = (cons (a) (l1))) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0_2))) (retval)) X_low_level_spec ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (((vnext + (i * sizeof(INT) ) )) # Int  |-> retval)
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT) ) ) (n_low_level_spec - (i + 1 ) ) l1 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0_2 )
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) ((i + 1 )) (vnext0) (retval)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= (i + 1 )) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext (i + 1 ) vnext0 )
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT) ) ) (n_low_level_spec - (i + 1 ) ) l0 )
.

Definition constr_return_wit_1_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext_2: Z) (i: Z) (vnext0: (@list Z)) (j: Z) ,
  [| (i >= n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_2 i vnext0 )
  **  (IntArray.full (vnext_2 + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  EX (vnext: (@list Z)) ,
  [| (safeExec ATrue (return (vnext)) X_low_level_spec ) |]
  &&  (IntArray.full vnext_2 n_low_level_spec vnext )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_1_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
|--
  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_2_low_level_spec_pure := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  ((( &( "vnext" ) )) # Ptr  |->_)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (retval > 0) |]
.

Definition constr_partial_solve_wit_2_low_level_spec_aux := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
|--
  [| (retval > 0) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_2_low_level_spec := constr_partial_solve_wit_2_low_level_spec_pure -> constr_partial_solve_wit_2_low_level_spec_aux.

Definition constr_partial_solve_wit_3_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (IntArray.full retval_2 retval l )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
|--
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (retval = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i retval_2 0 0 retval l )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_4_low_level_spec := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) ,
  [| (i < n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  [| (i < n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (((patn_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (str_low_level_spec) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i patn_pre i 0 (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
.

Definition constr_partial_solve_wit_5_low_level_spec_pure := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) ,
  [| (i < n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) X_low_level_spec ) |] 
  &&  [| (i <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (equiv (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) ) |]
.

Definition constr_partial_solve_wit_5_low_level_spec_aux := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) ,
  [| (i < n_low_level_spec) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) X_low_level_spec ) |] 
  &&  [| (i <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (equiv (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) ) |] 
  &&  [| (i < n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
.

Definition constr_partial_solve_wit_5_low_level_spec := constr_partial_solve_wit_5_low_level_spec_pure -> constr_partial_solve_wit_5_low_level_spec_aux.

Definition constr_partial_solve_wit_6_low_level_spec_pure := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  [| (i < n_low_level_spec) |]
.

Definition constr_partial_solve_wit_6_low_level_spec_aux := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  [| (i < n_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext i vnext0 )
.

Definition constr_partial_solve_wit_6_low_level_spec := constr_partial_solve_wit_6_low_level_spec_pure -> constr_partial_solve_wit_6_low_level_spec_aux.

Definition constr_which_implies_wit_1 := 
forall (n_low_level_spec: Z) (l0: (@list Z)) (i: Z) (vnext: Z) ,
  [| (i < n_low_level_spec) |]
  &&  (IntArray.full (vnext + (i * sizeof(INT) ) ) (n_low_level_spec - i ) l0 )
|--
  EX (a: Z)  (l1: (@list Z)) ,
  [| (l0 = (cons (a) (l1))) |]
  &&  (((vnext + (i * sizeof(INT) ) )) # Int  |-> a)
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT) ) ) (n_low_level_spec - (i + 1 ) ) l1 )
.

(*----- Function match -----*)

Definition match_safety_wit_1_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_safety_wit_2_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "patn_len" ) )) # Int  |-> retval_2)
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "text_len" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_safety_wit_3_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n_low_level_spec + 1 )) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  [| (((i - n_low_level_spec ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i - n_low_level_spec ) + 1 )) |]
.

Definition match_safety_wit_4_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n_low_level_spec + 1 )) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  [| ((i - n_low_level_spec ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - n_low_level_spec )) |]
.

Definition match_safety_wit_5_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n_low_level_spec + 1 )) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_safety_wit_6_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 <> n_low_level_spec) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n_low_level_spec + 1 )) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_safety_wit_7_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i >= m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition match_safety_wit_8_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i >= m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_entail_wit_1_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "patn_len" ) )) # Int  |-> retval_2)
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "text_len" ) )) # Int  |-> retval)
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (0) (0)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (0 >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_entail_wit_2_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 <> n_low_level_spec) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n_low_level_spec + 1 )) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
|--
  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) ((i + 1 )) (retval_3)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| ((i + 1 ) >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_return_wit_1_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 = n_low_level_spec) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n_low_level_spec + 1 )) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
|--
  EX (ret: (@option Z)) ,
  [| (safeExec ATrue (return (ret)) X_low_level_spec ) |] 
  &&  [| (((i - n_low_level_spec ) + 1 ) = (option_int_repr (ret))) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_return_wit_2_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i >= m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  EX (ret: (@option Z)) ,
  [| (safeExec ATrue (return (ret)) X_low_level_spec ) |] 
  &&  [| ((-1) = (option_int_repr (ret))) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_1_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_2_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_3_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i < m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (i < m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (text0_low_level_spec) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i text_pre i 0 (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_4_low_level_spec_pure := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i < m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (equiv (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) ) |]
.

Definition match_partial_solve_wit_4_low_level_spec_aux := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i < m_low_level_spec) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (equiv (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) ) |] 
  &&  [| (i < m_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n_low_level_spec) |] 
  &&  [| (0 <= (m_low_level_spec + 1 )) |] 
  &&  [| (retval = m_low_level_spec) |] 
  &&  [| (0 <= (n_low_level_spec + 1 )) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
.

Definition match_partial_solve_wit_4_low_level_spec := match_partial_solve_wit_4_low_level_spec_pure -> match_partial_solve_wit_4_low_level_spec_aux.

Definition match_derive_high_level_spec_by_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (m_high_level_spec: Z) (n_high_level_spec: Z) (vnext0_high_level_spec: (@list Z)) (text0_high_level_spec: (@list Z)) (patn0_high_level_spec: (@list Z)) ,
  [| (is_prefix_func vnext0_high_level_spec patn0_high_level_spec ) |] 
  &&  [| (n_high_level_spec > 0) |] 
  &&  [| (n_high_level_spec < INT_MAX) |] 
  &&  [| (m_high_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (patn0_high_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_high_level_spec + 1 ) (app (text0_high_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec )
|--
EX (patn0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (vnext0_low_level_spec: (@list Z)) (n_low_level_spec: Z) (m_low_level_spec: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |] 
  &&  [| (m_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec ))
  **
  ((EX ret retval_2,
  [| (safeExec ATrue (return (ret)) X_low_level_spec ) |] 
  &&  [| (retval_2 = (option_int_repr (ret))) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec ))
  -*
  ((EX retval,
  [| (retval >= 0) |] 
  &&  [| (first_occur patn0_high_level_spec text0_high_level_spec retval ) |]
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (patn0_high_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_high_level_spec + 1 ) (app (text0_high_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec ))
  ||
  (EX retval,
  [| (retval = (-1)) |] 
  &&  [| (no_occurance patn0_high_level_spec text0_high_level_spec ) |]
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (patn0_high_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_high_level_spec + 1 ) (app (text0_high_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec ))))
.

Definition constr_derive_high_level_spec_by_low_level_spec := 
forall (patn_pre: Z) (n_high_level_spec: Z) (str_high_level_spec: (@list Z)) ,
  [| (n_high_level_spec > 0) |] 
  &&  [| (n_high_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (str_high_level_spec) ((cons (0) (nil)))) )
|--
EX (str_low_level_spec: (@list Z)) (n_low_level_spec: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (n_low_level_spec > 0) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) ))
  **
  ((EX vnext_2 retval_2,
  [| (safeExec ATrue (return (vnext_2)) X_low_level_spec ) |]
  &&  (IntArray.full retval_2 n_low_level_spec vnext_2 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) ))
  -*
  (EX vnext retval,
  [| (is_prefix_func vnext str_high_level_spec ) |]
  &&  (IntArray.full retval n_high_level_spec vnext )
  **  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (str_high_level_spec) ((cons (0) (nil)))) )))
.

Definition inner_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (j_pre: Z) (ch_pre: Z) (vnext_pre: Z) (str_pre: Z) (f_bind_spec: (Z -> (@program unit B))) (X_bind_spec: (B -> (unit -> Prop))) (m_bind_spec: Z) (n_bind_spec: Z) (vnext0_bind_spec: (@list Z)) (str0_bind_spec: (@list Z)) ,
  [| (safeExec ATrue (bind ((inner_loop (0) (str0_bind_spec) (vnext0_bind_spec) (ch_pre) (j_pre))) (f_bind_spec)) X_bind_spec ) |] 
  &&  [| (m_bind_spec <= n_bind_spec) |] 
  &&  [| (n_bind_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_bind_spec + 1 ) (app (str0_bind_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec )
|--
EX (str0_low_level_spec: (@list Z)) (vnext0_low_level_spec: (@list Z)) (n_low_level_spec: Z) (m_low_level_spec: Z) (X_low_level_spec: (Z -> (unit -> Prop))) ,
  ([| (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch_pre) (j_pre)) X_low_level_spec ) |] 
  &&  [| (m_low_level_spec <= n_low_level_spec) |] 
  &&  [| (n_low_level_spec < INT_MAX) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec ))
  **
  ((EX retval_2,
  [| (safeExec ATrue (return (retval_2)) X_low_level_spec ) |] 
  &&  [| (0 <= retval_2) |] 
  &&  [| (retval_2 < (m_low_level_spec + 1 )) |]
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec ))
  -*
  (EX retval,
  [| (safeExec ATrue (applyf (f_bind_spec) (retval)) X_bind_spec ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (m_bind_spec + 1 )) |]
  &&  (CharArray.full str_pre (n_bind_spec + 1 ) (app (str0_bind_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include char_array_Strategy_Correct.
Include safeexecE_Strategy_Correct.

Axiom proof_of_inner_safety_wit_1_low_level_spec : inner_safety_wit_1_low_level_spec.
Axiom proof_of_inner_safety_wit_2_low_level_spec : inner_safety_wit_2_low_level_spec.
Axiom proof_of_inner_safety_wit_3_low_level_spec : inner_safety_wit_3_low_level_spec.
Axiom proof_of_inner_safety_wit_4_low_level_spec : inner_safety_wit_4_low_level_spec.
Axiom proof_of_inner_safety_wit_5_low_level_spec : inner_safety_wit_5_low_level_spec.
Axiom proof_of_inner_safety_wit_6_low_level_spec : inner_safety_wit_6_low_level_spec.
Axiom proof_of_inner_safety_wit_7_low_level_spec : inner_safety_wit_7_low_level_spec.
Axiom proof_of_inner_entail_wit_1_low_level_spec : inner_entail_wit_1_low_level_spec.
Axiom proof_of_inner_entail_wit_2_low_level_spec : inner_entail_wit_2_low_level_spec.
Axiom proof_of_inner_entail_wit_3_low_level_spec : inner_entail_wit_3_low_level_spec.
Axiom proof_of_inner_return_wit_1_low_level_spec : inner_return_wit_1_low_level_spec.
Axiom proof_of_inner_return_wit_2_low_level_spec : inner_return_wit_2_low_level_spec.
Axiom proof_of_inner_partial_solve_wit_1_low_level_spec : inner_partial_solve_wit_1_low_level_spec.
Axiom proof_of_inner_partial_solve_wit_2_low_level_spec : inner_partial_solve_wit_2_low_level_spec.
Axiom proof_of_constr_safety_wit_1_low_level_spec : constr_safety_wit_1_low_level_spec.
Axiom proof_of_constr_safety_wit_2_low_level_spec : constr_safety_wit_2_low_level_spec.
Axiom proof_of_constr_safety_wit_3_low_level_spec : constr_safety_wit_3_low_level_spec.
Axiom proof_of_constr_safety_wit_4_low_level_spec : constr_safety_wit_4_low_level_spec.
Axiom proof_of_constr_safety_wit_5_low_level_spec : constr_safety_wit_5_low_level_spec.
Axiom proof_of_constr_entail_wit_1_low_level_spec : constr_entail_wit_1_low_level_spec.
Axiom proof_of_constr_entail_wit_2_low_level_spec : constr_entail_wit_2_low_level_spec.
Axiom proof_of_constr_return_wit_1_low_level_spec : constr_return_wit_1_low_level_spec.
Axiom proof_of_constr_partial_solve_wit_1_low_level_spec : constr_partial_solve_wit_1_low_level_spec.
Axiom proof_of_constr_partial_solve_wit_2_low_level_spec_pure : constr_partial_solve_wit_2_low_level_spec_pure.
Axiom proof_of_constr_partial_solve_wit_2_low_level_spec : constr_partial_solve_wit_2_low_level_spec.
Axiom proof_of_constr_partial_solve_wit_3_low_level_spec : constr_partial_solve_wit_3_low_level_spec.
Axiom proof_of_constr_partial_solve_wit_4_low_level_spec : constr_partial_solve_wit_4_low_level_spec.
Axiom proof_of_constr_partial_solve_wit_5_low_level_spec_pure : constr_partial_solve_wit_5_low_level_spec_pure.
Axiom proof_of_constr_partial_solve_wit_5_low_level_spec : constr_partial_solve_wit_5_low_level_spec.
Axiom proof_of_constr_partial_solve_wit_6_low_level_spec_pure : constr_partial_solve_wit_6_low_level_spec_pure.
Axiom proof_of_constr_partial_solve_wit_6_low_level_spec : constr_partial_solve_wit_6_low_level_spec.
Axiom proof_of_constr_which_implies_wit_1 : constr_which_implies_wit_1.
Axiom proof_of_match_safety_wit_1_low_level_spec : match_safety_wit_1_low_level_spec.
Axiom proof_of_match_safety_wit_2_low_level_spec : match_safety_wit_2_low_level_spec.
Axiom proof_of_match_safety_wit_3_low_level_spec : match_safety_wit_3_low_level_spec.
Axiom proof_of_match_safety_wit_4_low_level_spec : match_safety_wit_4_low_level_spec.
Axiom proof_of_match_safety_wit_5_low_level_spec : match_safety_wit_5_low_level_spec.
Axiom proof_of_match_safety_wit_6_low_level_spec : match_safety_wit_6_low_level_spec.
Axiom proof_of_match_safety_wit_7_low_level_spec : match_safety_wit_7_low_level_spec.
Axiom proof_of_match_safety_wit_8_low_level_spec : match_safety_wit_8_low_level_spec.
Axiom proof_of_match_entail_wit_1_low_level_spec : match_entail_wit_1_low_level_spec.
Axiom proof_of_match_entail_wit_2_low_level_spec : match_entail_wit_2_low_level_spec.
Axiom proof_of_match_return_wit_1_low_level_spec : match_return_wit_1_low_level_spec.
Axiom proof_of_match_return_wit_2_low_level_spec : match_return_wit_2_low_level_spec.
Axiom proof_of_match_partial_solve_wit_1_low_level_spec : match_partial_solve_wit_1_low_level_spec.
Axiom proof_of_match_partial_solve_wit_2_low_level_spec : match_partial_solve_wit_2_low_level_spec.
Axiom proof_of_match_partial_solve_wit_3_low_level_spec : match_partial_solve_wit_3_low_level_spec.
Axiom proof_of_match_partial_solve_wit_4_low_level_spec_pure : match_partial_solve_wit_4_low_level_spec_pure.
Axiom proof_of_match_partial_solve_wit_4_low_level_spec : match_partial_solve_wit_4_low_level_spec.
Axiom proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.

End VC_Correct.
