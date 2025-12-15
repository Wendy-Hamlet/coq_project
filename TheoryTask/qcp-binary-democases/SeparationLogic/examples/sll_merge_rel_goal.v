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
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import sll_strategy_goal.
From SimpleC.EE Require Import sll_strategy_proof.
From SimpleC.EE Require Import safeexec_strategy_goal.
From SimpleC.EE Require Import safeexec_strategy_proof.

(*----- Function merge -----*)

Definition merge_safety_wit_1 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition merge_safety_wit_2 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_safety_wit_3 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (s1) (s2)) X ) |]
  &&  ((( &( "ret" ) )) # Ptr  |->_)
  **  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
  **  ((( &( "ret" ) )) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) ( &( "ret" ) ) l3 )
.

Definition merge_entail_wit_2_1 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y_next: Z) (y_data: Z) (l2_new: (@list Z)) ,
  [| (x_data < y_data) |] 
  &&  [| (l2_2 = (cons (y_data) (l2_new))) |] 
  &&  [| (l1_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X ) |]
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x_next l1 )
  **  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((x)  # "list" ->ₛ "next") l3 )
.

Definition merge_entail_wit_2_2 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y_next: Z) (y_data: Z) (l2_new: (@list Z)) ,
  [| (x_data >= y_data) |] 
  &&  [| (l2_2 = (cons (y_data) (l2_new))) |] 
  &&  [| (l1_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X ) |]
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x l1 )
  **  (sll y_next l2 )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((y)  # "list" ->ₛ "next") l3 )
.

Definition merge_return_wit_1 := 
forall (X: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) ,
  [| (x = 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sllseg ret y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)) ,
  [| (safeExec ATrue (return (s3)) X ) |]
  &&  (sll ret s3 )
.

Definition merge_return_wit_2 := 
forall (X: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sllseg ret x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)) ,
  [| (safeExec ATrue (return (s3)) X ) |]
  &&  (sll ret s3 )
.

Definition merge_partial_solve_wit_1_pure := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (x <> 0) |]
.

Definition merge_partial_solve_wit_1_aux := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (x <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_partial_solve_wit_1 := merge_partial_solve_wit_1_pure -> merge_partial_solve_wit_1_aux.

Definition merge_partial_solve_wit_2_pure := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (y <> 0) |]
.

Definition merge_partial_solve_wit_2_aux := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (y <> 0) |] 
  &&  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_partial_solve_wit_2 := merge_partial_solve_wit_2_pure -> merge_partial_solve_wit_2_aux.

Definition merge_partial_solve_wit_3 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_partial_solve_wit_4 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (x = 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (x = 0) |] 
  &&  [| (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) |]
  &&  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l1 )
|--
  EX (x_next: Z)  (x_data: Z)  (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
.

Definition merge_which_implies_wit_2 := 
forall (l2: (@list Z)) (y: Z) ,
  [| (y <> 0) |]
  &&  (sll y l2 )
|--
  EX (y_next: Z)  (y_data: Z)  (l2_new: (@list Z)) ,
  [| (l2 = (cons (y_data) (l2_new))) |]
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
.

Definition merge_which_implies_wit_3 := 
forall (u: Z) (l3: (@list Z)) (t: Z) ,
  ((t) # Ptr  |-> u)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z) ,
  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sllseg ret u l3 )
.

(*----- Function split_rec -----*)

Definition split_rec_safety_wit_1_low_level_spec := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition split_rec_return_wit_1_low_level_spec := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (p_pre_v_2: Z) (q_pre_v_2: Z) ,
  [| (x_pre = 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
  **  (sll p_pre_v_2 l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v_2)
  **  (sll q_pre_v_2 l2_low_level_spec )
|--
  EX (q_pre_v: Z)  (p_pre_v: Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  [| (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
.

Definition split_rec_return_wit_2_low_level_spec := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_data: Z) (l_new: (@list Z)) (q_callee_v: Z) (p_callee_v: Z) (s1_2: (@list Z)) (s2_2: (@list Z)) ,
  [| (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((q_pre) # Ptr  |-> p_callee_v)
  **  (sll p_callee_v s1_2 )
  **  ((p_pre) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v s2_2 )
|--
  EX (q_pre_v: Z)  (p_pre_v: Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  [| (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
.

Definition split_rec_partial_solve_wit_1_low_level_spec_pure := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (x_pre <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (x_pre <> 0) |]
.

Definition split_rec_partial_solve_wit_1_low_level_spec_aux := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (x_pre <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
.

Definition split_rec_partial_solve_wit_1_low_level_spec := split_rec_partial_solve_wit_1_low_level_spec_pure -> split_rec_partial_solve_wit_1_low_level_spec_aux.

Definition split_rec_partial_solve_wit_2_low_level_spec_pure := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "t" ) )) # Ptr  |-> x_next)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v)
  **  (sll x_next l_new )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll p_pre_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
.

Definition split_rec_partial_solve_wit_2_low_level_spec_aux := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v)
  **  (sll x_next l_new )
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll p_pre_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((p_pre) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_low_level_spec )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
.

Definition split_rec_partial_solve_wit_2_low_level_spec := split_rec_partial_solve_wit_2_low_level_spec_pure -> split_rec_partial_solve_wit_2_low_level_spec_aux.

Definition split_rec_partial_solve_wit_3_low_level_spec_pure := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
  **  (sll x_next l_new )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) |]
.

Definition split_rec_partial_solve_wit_3_low_level_spec_aux := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec )
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
.

Definition split_rec_partial_solve_wit_3_low_level_spec := split_rec_partial_solve_wit_3_low_level_spec_pure -> split_rec_partial_solve_wit_3_low_level_spec_aux.

Definition split_rec_which_implies_wit_1 := 
forall (l: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l )
|--
  EX (x_next: Z)  (x_data: Z)  (l_new: (@list Z)) ,
  [| (l = (cons (x_data) (l_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l_new )
.

Definition split_rec_which_implies_wit_2 := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_data: Z) (l_new: (@list Z)) (p: Z) (p_v: Z) (p_v_next: Z) (t: Z) ,
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |] 
  &&  [| (l_low_level_spec = (cons (x_data) (l_new))) |] 
  &&  [| (p_v <> 0) |]
  &&  ((p) # Ptr  |-> p_v)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1_low_level_spec )
  **  (sll t l_new )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) |]
  &&  ((p) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1_low_level_spec)) )
  **  (sll t l_new )
.

(*----- Function merge_sort -----*)

Definition merge_sort_safety_wit_1_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort_safety_wit_2_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 nil )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort_safety_wit_3_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (p_callee_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_callee_v)
  **  (sll p_callee_v s1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v s2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort_entail_wit_1_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll 0 nil )
  **  (sll x_pre l_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort_entail_wit_2_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (p_callee_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (q_callee_v <> 0) |] 
  &&  [| (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec ) |]
  &&  (sll p_callee_v s1 )
  **  (sll q_callee_v s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll p_callee_v l1 )
  **  (sll q_callee_v l2 )
.

Definition merge_sort_entail_wit_3_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (l2_2: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval l0 )
  **  (sll q_callee_v l2_2 )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval l1 )
  **  (sll q_callee_v l2 )
.

Definition merge_sort_entail_wit_4_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (retval: Z) (l1_2: (@list Z)) (l0: (@list Z)) (retval_2: Z) ,
  [| (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval_2 l0 )
  **  (sll retval l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval l1 )
  **  (sll retval_2 l2 )
.

Definition merge_sort_return_wit_1_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (p_callee_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (q_callee_v = 0) |] 
  &&  [| (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec ) |]
  &&  (sll p_callee_v s1 )
  **  (sll q_callee_v s2 )
|--
  EX (l0: (@list Z)) ,
  [| (safeExec ATrue (return (l0)) X_low_level_spec ) |]
  &&  (sll p_callee_v l0 )
.

Definition merge_sort_return_wit_2_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (s3: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (return (s3)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval s3 )
|--
  EX (l0: (@list Z)) ,
  [| (safeExec ATrue (return (l0)) X_low_level_spec ) |]
  &&  (sll retval l0 )
.

Definition merge_sort_partial_solve_wit_1_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  [| (0 = 0) |]
.

Definition merge_sort_partial_solve_wit_1_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
|--
  [| (0 = 0) |] 
  &&  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort_partial_solve_wit_1_low_level_spec := merge_sort_partial_solve_wit_1_low_level_spec_pure -> merge_sort_partial_solve_wit_1_low_level_spec_aux.

Definition merge_sort_partial_solve_wit_2_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 nil )
  **  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  [| (0 = 0) |]
.

Definition merge_sort_partial_solve_wit_2_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll 0 nil )
  **  (sll x_pre l_low_level_spec )
|--
  [| (0 = 0) |] 
  &&  [| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort_partial_solve_wit_2_low_level_spec := merge_sort_partial_solve_wit_2_low_level_spec_pure -> merge_sort_partial_solve_wit_2_low_level_spec_aux.

Definition merge_sort_partial_solve_wit_3_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) |]
  &&  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) (nil) (nil))) (mergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (equiv (split_rel (l_low_level_spec)) (split_rec_rel (l_low_level_spec) (nil) (nil)) ) |] 
  &&  [| (equiv mergesortrec_loc0 mergesortrec_loc0 ) |]
.

Definition merge_sort_partial_solve_wit_3_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) (nil) (nil))) (mergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (equiv (split_rel (l_low_level_spec)) (split_rec_rel (l_low_level_spec) (nil) (nil)) ) |] 
  &&  [| (equiv mergesortrec_loc0 mergesortrec_loc0 ) |]
  &&  (sll x_pre l_low_level_spec )
  **  (sll 0 nil )
  **  (sll 0 nil )
.

Definition merge_sort_partial_solve_wit_3_low_level_spec := merge_sort_partial_solve_wit_3_low_level_spec_pure -> merge_sort_partial_solve_wit_3_low_level_spec_aux.

Definition merge_sort_partial_solve_wit_4_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (p_callee_v: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_callee_v)
  **  (sll p_callee_v l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) |]
.

Definition merge_sort_partial_solve_wit_4_low_level_spec_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (p_callee_v: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll p_callee_v l1 )
  **  (sll q_callee_v l2 )
|--
  [| (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll p_callee_v l1 )
  **  (sll q_callee_v l2 )
.

Definition merge_sort_partial_solve_wit_4_low_level_spec := merge_sort_partial_solve_wit_4_low_level_spec_pure -> merge_sort_partial_solve_wit_4_low_level_spec_aux.

Definition merge_sort_partial_solve_wit_5_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (retval: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |]
.

Definition merge_sort_partial_solve_wit_5_low_level_spec_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (retval: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval l1 )
  **  (sll q_callee_v l2 )
|--
  [| (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll q_callee_v l2 )
  **  (sll retval l1 )
.

Definition merge_sort_partial_solve_wit_5_low_level_spec := merge_sort_partial_solve_wit_5_low_level_spec_pure -> merge_sort_partial_solve_wit_5_low_level_spec_aux.

Definition merge_sort_partial_solve_wit_6_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (retval: Z) (retval_2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval l1 )
  **  ((( &( "q" ) )) # Ptr  |-> retval_2)
  **  (sll retval_2 l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |]
.

Definition merge_sort_partial_solve_wit_6_low_level_spec_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_callee_v: Z) (retval: Z) (retval_2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval l1 )
  **  (sll retval_2 l2 )
|--
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (q_callee_v <> 0) |]
  &&  (sll retval l1 )
  **  (sll retval_2 l2 )
.

Definition merge_sort_partial_solve_wit_6_low_level_spec := merge_sort_partial_solve_wit_6_low_level_spec_pure -> merge_sort_partial_solve_wit_6_low_level_spec_aux.

Definition merge_sort_which_implies_wit_1 := 
forall (p: Z) ,
  [| (p = 0) |]
  &&  emp
|--
  (sll p nil )
.

Definition merge_sort_which_implies_wit_2 := 
forall (q: Z) ,
  [| (q = 0) |]
  &&  emp
|--
  (sll q nil )
.

(*----- Function merge_sort3 -----*)

Definition merge_sort3_safety_wit_1_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition merge_sort3_safety_wit_2_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort3_safety_wit_3_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 nil )
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort3_entail_wit_1_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll 0 nil )
  **  (sll x_pre l_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_entail_wit_2_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_callee_v: Z) (p_callee_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll p_callee_v s1 )
  **  (sll q_callee_v s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll p_callee_v l1 )
  **  (sll q_callee_v l2 )
.

Definition merge_sort3_entail_wit_3_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_callee_v: Z) (l2_2: (@list Z)) (l0: (@list Z)) (retval_2: Z) ,
  [| (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_2 l0 )
  **  (sll q_callee_v l2_2 )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_2 l1 )
  **  (sll q_callee_v l2 )
.

Definition merge_sort3_entail_wit_4_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (l1_2: (@list Z)) (l0: (@list Z)) (retval_3: Z) ,
  [| (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_3 l0 )
  **  (sll retval_2 l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_2 l1 )
  **  (sll retval_3 l2 )
.

Definition merge_sort3_return_wit_1_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (Permutation l_low_level_spec l0_2 ) |] 
  &&  [| (incr l0_2 ) |] 
  &&  [| (retval_2 <= 8) |] 
  &&  [| (retval_2 = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll retval l0_2 )
|--
  EX (l0: (@list Z)) ,
  [| (safeExec ATrue (return (l0)) X_low_level_spec ) |]
  &&  (sll retval l0 )
.

Definition merge_sort3_return_wit_2_low_level_spec := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (s3: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (return (s3)) X_low_level_spec ) |] 
  &&  [| (retval_2 > 8) |] 
  &&  [| (retval_2 = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval s3 )
|--
  EX (l0: (@list Z)) ,
  [| (safeExec ATrue (return (l0)) X_low_level_spec ) |]
  &&  (sll retval l0 )
.

Definition merge_sort3_partial_solve_wit_1_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
.

Definition merge_sort3_partial_solve_wit_1_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) ,
  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
|--
  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_1_low_level_spec := merge_sort3_partial_solve_wit_1_low_level_spec_pure -> merge_sort3_partial_solve_wit_1_low_level_spec_aux.

Definition merge_sort3_partial_solve_wit_2_low_level_spec := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval <= 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
|--
  [| (retval <= 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_3_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 = 0) |]
.

Definition merge_sort3_partial_solve_wit_3_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
|--
  [| (0 = 0) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_3_low_level_spec := merge_sort3_partial_solve_wit_3_low_level_spec_pure -> merge_sort3_partial_solve_wit_3_low_level_spec_aux.

Definition merge_sort3_partial_solve_wit_4_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 nil )
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 = 0) |]
.

Definition merge_sort3_partial_solve_wit_4_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll 0 nil )
  **  (sll x_pre l_low_level_spec )
|--
  [| (0 = 0) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_4_low_level_spec := merge_sort3_partial_solve_wit_4_low_level_spec_pure -> merge_sort3_partial_solve_wit_4_low_level_spec_aux.

Definition merge_sort3_partial_solve_wit_5_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) (nil) (nil))) (gmergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (equiv (split_rel (l_low_level_spec)) (split_rec_rel (l_low_level_spec) (nil) (nil)) ) |] 
  &&  [| (equiv gmergesortrec_loc0 gmergesortrec_loc0 ) |]
.

Definition merge_sort3_partial_solve_wit_5_low_level_spec_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) ,
  [| (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll x_pre l_low_level_spec )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) (nil) (nil))) (gmergesortrec_loc0)) X_low_level_spec ) |] 
  &&  [| (equiv (split_rel (l_low_level_spec)) (split_rec_rel (l_low_level_spec) (nil) (nil)) ) |] 
  &&  [| (equiv gmergesortrec_loc0 gmergesortrec_loc0 ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll x_pre l_low_level_spec )
  **  (sll 0 nil )
  **  (sll 0 nil )
.

Definition merge_sort3_partial_solve_wit_5_low_level_spec := merge_sort3_partial_solve_wit_5_low_level_spec_pure -> merge_sort3_partial_solve_wit_5_low_level_spec_aux.

Definition merge_sort3_partial_solve_wit_6_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_callee_v: Z) (p_callee_v: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_callee_v)
  **  (sll p_callee_v l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (equiv (gmergesortrec_loc1 (l2)) (gmergesortrec_loc1 (l2)) ) |]
.

Definition merge_sort3_partial_solve_wit_6_low_level_spec_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_callee_v: Z) (p_callee_v: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll p_callee_v l1 )
  **  (sll q_callee_v l2 )
|--
  [| (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) |] 
  &&  [| (equiv (gmergesortrec_loc1 (l2)) (gmergesortrec_loc1 (l2)) ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll p_callee_v l1 )
  **  (sll q_callee_v l2 )
.

Definition merge_sort3_partial_solve_wit_6_low_level_spec := merge_sort3_partial_solve_wit_6_low_level_spec_pure -> merge_sort3_partial_solve_wit_6_low_level_spec_aux.

Definition merge_sort3_partial_solve_wit_7_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_callee_v: Z) (retval_2: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (sll retval_2 l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |]
.

Definition merge_sort3_partial_solve_wit_7_low_level_spec_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_callee_v: Z) (retval_2: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_2 l1 )
  **  (sll q_callee_v l2 )
|--
  [| (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll q_callee_v l2 )
  **  (sll retval_2 l1 )
.

Definition merge_sort3_partial_solve_wit_7_low_level_spec := merge_sort3_partial_solve_wit_7_low_level_spec_pure -> merge_sort3_partial_solve_wit_7_low_level_spec_aux.

Definition merge_sort3_partial_solve_wit_8_low_level_spec_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (sll retval_2 l1 )
  **  ((( &( "q" ) )) # Ptr  |-> retval_3)
  **  (sll retval_3 l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |]
.

Definition merge_sort3_partial_solve_wit_8_low_level_spec_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_2 l1 )
  **  (sll retval_3 l2 )
|--
  [| (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (retval > 8) |] 
  &&  [| (retval = (Zlength (l_low_level_spec))) |] 
  &&  [| ((Zlength (l_low_level_spec)) <= INT_MAX) |]
  &&  (sll retval_2 l1 )
  **  (sll retval_3 l2 )
.

Definition merge_sort3_partial_solve_wit_8_low_level_spec := merge_sort3_partial_solve_wit_8_low_level_spec_pure -> merge_sort3_partial_solve_wit_8_low_level_spec_aux.

Definition merge_sort3_which_implies_wit_1 := 
forall (p: Z) ,
  [| (p = 0) |]
  &&  emp
|--
  (sll p nil )
.

Definition merge_sort3_which_implies_wit_2 := 
forall (q: Z) ,
  [| (q = 0) |]
  &&  emp
|--
  (sll q nil )
.

Definition merge_sort3_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@program unit B))) (l_low_level_spec_aux: (@list Z)) ,
  [| ((Zlength (l_low_level_spec_aux)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (bind ((gmergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) |]
  &&  (sll x_pre l_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  [| (safeExec ATrue (return (l0_2)) X_low_level_spec ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) |]
  &&  (sll retval l0 )))
.

Definition merge_sort3_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l_high_level_spec: (@list Z)) ,
  [| ((Zlength (l_high_level_spec)) <= INT_MAX) |]
  &&  (sll x_pre l_high_level_spec )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| ((Zlength (l_low_level_spec)) <= INT_MAX) |] 
  &&  [| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  [| (safeExec ATrue (return (l0_2)) X_low_level_spec ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (Permutation l_high_level_spec l0 ) |] 
  &&  [| (incr l0 ) |]
  &&  (sll retval l0 )))
.

Definition merge_sort2_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@program unit B))) (l_low_level_spec_aux: (@list Z)) ,
  [| (safeExec ATrue (bind ((gmergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) |]
  &&  (sll x_pre l_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  [| (safeExec ATrue (return (l0_2)) X_low_level_spec ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) |]
  &&  (sll retval l0 )))
.

Definition merge_sort2_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l_high_level_spec: (@list Z)) ,
  (sll x_pre l_high_level_spec )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  [| (safeExec ATrue (return (l0_2)) X_low_level_spec ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (Permutation l_high_level_spec l0 ) |] 
  &&  [| (incr l0 ) |]
  &&  (sll retval l0 )))
.

Definition merge_sort_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@program unit B))) (l_low_level_spec_aux: (@list Z)) ,
  [| (safeExec ATrue (bind ((mergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) |]
  &&  (sll x_pre l_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  [| (safeExec ATrue (return (l0_2)) X_low_level_spec ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) |]
  &&  (sll retval l0 )))
.

Definition merge_sort_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l_high_level_spec: (@list Z)) ,
  (sll x_pre l_high_level_spec )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  [| (safeExec ATrue (return (l0_2)) X_low_level_spec ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (Permutation l_high_level_spec l0 ) |] 
  &&  [| (incr l0 ) |]
  &&  (sll retval l0 )))
.

Definition split_rec_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: (((@list Z) * (@list Z)) -> (@program unit B))) (l2_low_level_spec_aux: (@list Z)) (l1_low_level_spec_aux: (@list Z)) (l_low_level_spec_aux: (@list Z)) ,
  EX q_pre_v p_pre_v,
  [| (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec_aux) (l1_low_level_spec_aux) (l2_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) |]
  &&  (sll x_pre l_low_level_spec_aux )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_low_level_spec_aux )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) ,
  (EX q_callee_v p_callee_v,
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_callee_v)
  **  (sll p_callee_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v l2_low_level_spec ))
  **
  ((EX q_callee_v_2 p_callee_v_2 s1_2 s2_2,
  [| (safeExec ATrue (return ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) |]
  &&  ((p_pre) # Ptr  |-> p_callee_v_2)
  **  (sll p_callee_v_2 s1_2 )
  **  ((q_pre) # Ptr  |-> q_callee_v_2)
  **  (sll q_callee_v_2 s2_2 ))
  -*
  (EX q_pre_v_2 p_pre_v_2 s1 s2,
  [| (safeExec ATrue (applyf (c_low_level_spec_aux) ((maketuple (s1) (s2)))) X_low_level_spec_aux ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v_2)
  **  (sll p_pre_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v_2)
  **  (sll q_pre_v_2 s2 )))
.

Definition split_rec_derive_high_level_spec_by_low_level_spec := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_high_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_high_level_spec: (@list Z)) ,
  EX q_pre_v p_pre_v,
  [| (safeExec ATrue (split_rel (l_high_level_spec)) X_high_level_spec ) |]
  &&  (sll x_pre l_high_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v nil )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v nil )
|--
EX (l_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) ,
  (EX q_callee_v p_callee_v,
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_callee_v)
  **  (sll p_callee_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_callee_v)
  **  (sll q_callee_v l2_low_level_spec ))
  **
  ((EX q_callee_v_2 p_callee_v_2 s1_2 s2_2,
  [| (safeExec ATrue (return ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) |]
  &&  ((p_pre) # Ptr  |-> p_callee_v_2)
  **  (sll p_callee_v_2 s1_2 )
  **  ((q_pre) # Ptr  |-> q_callee_v_2)
  **  (sll q_callee_v_2 s2_2 ))
  -*
  (EX q_pre_v_2 p_pre_v_2 s1 s2,
  [| (safeExec ATrue (return ((maketuple (s1) (s2)))) X_high_level_spec ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v_2)
  **  (sll p_pre_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v_2)
  **  (sll q_pre_v_2 s2 )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Axiom proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Axiom proof_of_merge_safety_wit_3 : merge_safety_wit_3.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Axiom proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Axiom proof_of_merge_return_wit_1 : merge_return_wit_1.
Axiom proof_of_merge_return_wit_2 : merge_return_wit_2.
Axiom proof_of_merge_partial_solve_wit_1_pure : merge_partial_solve_wit_1_pure.
Axiom proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Axiom proof_of_merge_partial_solve_wit_2_pure : merge_partial_solve_wit_2_pure.
Axiom proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Axiom proof_of_merge_partial_solve_wit_3 : merge_partial_solve_wit_3.
Axiom proof_of_merge_partial_solve_wit_4 : merge_partial_solve_wit_4.
Axiom proof_of_merge_which_implies_wit_1 : merge_which_implies_wit_1.
Axiom proof_of_merge_which_implies_wit_2 : merge_which_implies_wit_2.
Axiom proof_of_merge_which_implies_wit_3 : merge_which_implies_wit_3.
Axiom proof_of_split_rec_safety_wit_1_low_level_spec : split_rec_safety_wit_1_low_level_spec.
Axiom proof_of_split_rec_return_wit_1_low_level_spec : split_rec_return_wit_1_low_level_spec.
Axiom proof_of_split_rec_return_wit_2_low_level_spec : split_rec_return_wit_2_low_level_spec.
Axiom proof_of_split_rec_partial_solve_wit_1_low_level_spec_pure : split_rec_partial_solve_wit_1_low_level_spec_pure.
Axiom proof_of_split_rec_partial_solve_wit_1_low_level_spec : split_rec_partial_solve_wit_1_low_level_spec.
Axiom proof_of_split_rec_partial_solve_wit_2_low_level_spec_pure : split_rec_partial_solve_wit_2_low_level_spec_pure.
Axiom proof_of_split_rec_partial_solve_wit_2_low_level_spec : split_rec_partial_solve_wit_2_low_level_spec.
Axiom proof_of_split_rec_partial_solve_wit_3_low_level_spec_pure : split_rec_partial_solve_wit_3_low_level_spec_pure.
Axiom proof_of_split_rec_partial_solve_wit_3_low_level_spec : split_rec_partial_solve_wit_3_low_level_spec.
Axiom proof_of_split_rec_which_implies_wit_1 : split_rec_which_implies_wit_1.
Axiom proof_of_split_rec_which_implies_wit_2 : split_rec_which_implies_wit_2.
Axiom proof_of_merge_sort_safety_wit_1_low_level_spec : merge_sort_safety_wit_1_low_level_spec.
Axiom proof_of_merge_sort_safety_wit_2_low_level_spec : merge_sort_safety_wit_2_low_level_spec.
Axiom proof_of_merge_sort_safety_wit_3_low_level_spec : merge_sort_safety_wit_3_low_level_spec.
Axiom proof_of_merge_sort_entail_wit_1_low_level_spec : merge_sort_entail_wit_1_low_level_spec.
Axiom proof_of_merge_sort_entail_wit_2_low_level_spec : merge_sort_entail_wit_2_low_level_spec.
Axiom proof_of_merge_sort_entail_wit_3_low_level_spec : merge_sort_entail_wit_3_low_level_spec.
Axiom proof_of_merge_sort_entail_wit_4_low_level_spec : merge_sort_entail_wit_4_low_level_spec.
Axiom proof_of_merge_sort_return_wit_1_low_level_spec : merge_sort_return_wit_1_low_level_spec.
Axiom proof_of_merge_sort_return_wit_2_low_level_spec : merge_sort_return_wit_2_low_level_spec.
Axiom proof_of_merge_sort_partial_solve_wit_1_low_level_spec_pure : merge_sort_partial_solve_wit_1_low_level_spec_pure.
Axiom proof_of_merge_sort_partial_solve_wit_1_low_level_spec : merge_sort_partial_solve_wit_1_low_level_spec.
Axiom proof_of_merge_sort_partial_solve_wit_2_low_level_spec_pure : merge_sort_partial_solve_wit_2_low_level_spec_pure.
Axiom proof_of_merge_sort_partial_solve_wit_2_low_level_spec : merge_sort_partial_solve_wit_2_low_level_spec.
Axiom proof_of_merge_sort_partial_solve_wit_3_low_level_spec_pure : merge_sort_partial_solve_wit_3_low_level_spec_pure.
Axiom proof_of_merge_sort_partial_solve_wit_3_low_level_spec : merge_sort_partial_solve_wit_3_low_level_spec.
Axiom proof_of_merge_sort_partial_solve_wit_4_low_level_spec_pure : merge_sort_partial_solve_wit_4_low_level_spec_pure.
Axiom proof_of_merge_sort_partial_solve_wit_4_low_level_spec : merge_sort_partial_solve_wit_4_low_level_spec.
Axiom proof_of_merge_sort_partial_solve_wit_5_low_level_spec_pure : merge_sort_partial_solve_wit_5_low_level_spec_pure.
Axiom proof_of_merge_sort_partial_solve_wit_5_low_level_spec : merge_sort_partial_solve_wit_5_low_level_spec.
Axiom proof_of_merge_sort_partial_solve_wit_6_low_level_spec_pure : merge_sort_partial_solve_wit_6_low_level_spec_pure.
Axiom proof_of_merge_sort_partial_solve_wit_6_low_level_spec : merge_sort_partial_solve_wit_6_low_level_spec.
Axiom proof_of_merge_sort_which_implies_wit_1 : merge_sort_which_implies_wit_1.
Axiom proof_of_merge_sort_which_implies_wit_2 : merge_sort_which_implies_wit_2.
Axiom proof_of_merge_sort3_safety_wit_1_low_level_spec : merge_sort3_safety_wit_1_low_level_spec.
Axiom proof_of_merge_sort3_safety_wit_2_low_level_spec : merge_sort3_safety_wit_2_low_level_spec.
Axiom proof_of_merge_sort3_safety_wit_3_low_level_spec : merge_sort3_safety_wit_3_low_level_spec.
Axiom proof_of_merge_sort3_entail_wit_1_low_level_spec : merge_sort3_entail_wit_1_low_level_spec.
Axiom proof_of_merge_sort3_entail_wit_2_low_level_spec : merge_sort3_entail_wit_2_low_level_spec.
Axiom proof_of_merge_sort3_entail_wit_3_low_level_spec : merge_sort3_entail_wit_3_low_level_spec.
Axiom proof_of_merge_sort3_entail_wit_4_low_level_spec : merge_sort3_entail_wit_4_low_level_spec.
Axiom proof_of_merge_sort3_return_wit_1_low_level_spec : merge_sort3_return_wit_1_low_level_spec.
Axiom proof_of_merge_sort3_return_wit_2_low_level_spec : merge_sort3_return_wit_2_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_1_low_level_spec_pure : merge_sort3_partial_solve_wit_1_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_1_low_level_spec : merge_sort3_partial_solve_wit_1_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_2_low_level_spec : merge_sort3_partial_solve_wit_2_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_3_low_level_spec_pure : merge_sort3_partial_solve_wit_3_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_3_low_level_spec : merge_sort3_partial_solve_wit_3_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_4_low_level_spec_pure : merge_sort3_partial_solve_wit_4_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_4_low_level_spec : merge_sort3_partial_solve_wit_4_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_5_low_level_spec_pure : merge_sort3_partial_solve_wit_5_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_5_low_level_spec : merge_sort3_partial_solve_wit_5_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_6_low_level_spec_pure : merge_sort3_partial_solve_wit_6_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_6_low_level_spec : merge_sort3_partial_solve_wit_6_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_7_low_level_spec_pure : merge_sort3_partial_solve_wit_7_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_7_low_level_spec : merge_sort3_partial_solve_wit_7_low_level_spec.
Axiom proof_of_merge_sort3_partial_solve_wit_8_low_level_spec_pure : merge_sort3_partial_solve_wit_8_low_level_spec_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_8_low_level_spec : merge_sort3_partial_solve_wit_8_low_level_spec.
Axiom proof_of_merge_sort3_which_implies_wit_1 : merge_sort3_which_implies_wit_1.
Axiom proof_of_merge_sort3_which_implies_wit_2 : merge_sort3_which_implies_wit_2.
Axiom proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_merge_sort3_derive_high_level_spec_by_low_level_spec : merge_sort3_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_merge_sort2_derive_low_level_spec_aux_by_low_level_spec : merge_sort2_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_merge_sort2_derive_high_level_spec_by_low_level_spec : merge_sort2_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_merge_sort_derive_low_level_spec_aux_by_low_level_spec : merge_sort_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_split_rec_derive_low_level_spec_aux_by_low_level_spec : split_rec_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_split_rec_derive_high_level_spec_by_low_level_spec : split_rec_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
