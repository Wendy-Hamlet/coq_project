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
Require Import sll_project_lib.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import sll_project_strategy_goal.
Require Import sll_project_strategy_proof.

(*----- Function nil_list -----*)

Definition nil_list_safety_wit_1 := 
  TT && emp 
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition nil_list_return_wit_1 := 
  TT && emp 
|--
  (sll 0 nil )
.

(*----- Function cons_list -----*)

Definition cons_list_return_wit_1 := 
forall (next_pre: Z) (data_pre: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "sll" ->ₛ "data")) # UInt  |-> data_pre)
  **  ((&((retval)  # "sll" ->ₛ "next")) # Ptr  |-> next_pre)
  **  (sll next_pre l )
|--
  (sll retval (cons (data_pre) (l)) )
.

Definition cons_list_partial_solve_wit_1 := 
forall (next_pre: Z) (l: (@list Z)) ,
  (sll next_pre l )
|--
  (sll next_pre l )
.

(*----- Function free_list -----*)

Definition free_list_entail_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) ,
  (sll head_pre l )
|--
  EX (l_rest: (@list Z)) ,
  (sll head_pre l_rest )
.

Definition free_list_entail_wit_2 := 
forall (head: Z) (l_rest_2: (@list Z)) (head_next: Z) (head_data: Z) (l_rest_new: (@list Z)) ,
  [| (l_rest_2 = (cons (head_data) (l_rest_new))) |] 
  &&  [| (head <> 0) |]
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
|--
  EX (l_rest: (@list Z)) ,
  (sll head_next l_rest )
.

Definition free_list_return_wit_1 := 
forall (head: Z) (l_rest: (@list Z)) ,
  [| (head = 0) |]
  &&  (sll head l_rest )
|--
  TT && emp 
.

Definition free_list_partial_solve_wit_1_pure := 
forall (head: Z) (l_rest: (@list Z)) ,
  [| (head <> 0) |]
  &&  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sll head l_rest )
|--
  [| (head <> 0) |]
.

Definition free_list_partial_solve_wit_1_aux := 
forall (head: Z) (l_rest: (@list Z)) ,
  [| (head <> 0) |]
  &&  (sll head l_rest )
|--
  [| (head <> 0) |] 
  &&  [| (head <> 0) |]
  &&  (sll head l_rest )
.

Definition free_list_partial_solve_wit_1 := free_list_partial_solve_wit_1_pure -> free_list_partial_solve_wit_1_aux.

Definition free_list_partial_solve_wit_2 := 
forall (head: Z) (l_rest: (@list Z)) (head_next: Z) (head_data: Z) (l_rest_new: (@list Z)) ,
  [| (l_rest = (cons (head_data) (l_rest_new))) |] 
  &&  [| (head <> 0) |]
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
|--
  [| (l_rest = (cons (head_data) (l_rest_new))) |] 
  &&  [| (head <> 0) |]
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
.

Definition free_list_which_implies_wit_1 := 
forall (l_rest: (@list Z)) (head: Z) ,
  [| (head <> 0) |]
  &&  (sll head l_rest )
|--
  EX (head_next: Z)  (head_data: Z)  (l_rest_new: (@list Z)) ,
  [| (l_rest = (cons (head_data) (l_rest_new))) |]
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
.

(*----- Function map_list -----*)

Definition map_list_safety_wit_1 := 
forall (l: (@list Z)) (head: Z) (p: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |]
  &&  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition map_list_entail_wit_1 := 
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) ,
  (sll head_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |]
  &&  (sllseg head_pre head_pre (map_mult (x_pre) (l1)) )
  **  (sll head_pre l2 )
.

Definition map_list_entail_wit_2 := 
forall (l: (@list Z)) (head: Z) (p: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l2_new: (@list Z)) ,
  [| (l2_2 = (cons (p_data) (l2_new))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |]
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> (unsigned_last_nbits ((x * p_data )) (32)))
  **  (sllseg head p (map_mult (x) (l1_2)) )
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l2_new )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |]
  &&  (sllseg head p_next (map_mult (x) (l1)) )
  **  (sll p_next l2 )
.

Definition map_list_return_wit_1 := 
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (head: Z) (p: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p = 0) |] 
  &&  [| (l = (app (l1) (l2))) |]
  &&  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
|--
  (sll head_pre (map_mult (x_pre) (l)) )
.

Definition map_list_partial_solve_wit_1_pure := 
forall (l: (@list Z)) (head: Z) (p: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |]
  &&  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
|--
  [| (l = (app (l1) (l2))) |] 
  &&  [| (p <> 0) |]
.

Definition map_list_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (head: Z) (p: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |]
  &&  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
|--
  [| (l = (app (l1) (l2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |]
  &&  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
.

Definition map_list_partial_solve_wit_1 := map_list_partial_solve_wit_1_pure -> map_list_partial_solve_wit_1_aux.

Definition map_list_which_implies_wit_1 := 
forall (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (x: Z) (p: Z) (head: Z) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (p <> 0) |]
  &&  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l2_new: (@list Z)) ,
  [| (l2 = (cons (p_data) (l2_new))) |]
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  (sllseg head p (map_mult (x) (l1)) )
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l2_new )
.

(*----- Function nil_list_box -----*)

Definition nil_list_box_return_wit_1 := 
forall (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval <> 0) |]
  &&  (sllb retval nil )
|--
  (sllb retval nil )
.

Definition nil_list_box_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition nil_list_box_partial_solve_wit_2 := 
forall (retval: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> 0)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
|--
  [| (retval <> 0) |]
  &&  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> 0)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
.

Definition nil_list_box_partial_solve_wit_3_pure := 
forall (retval: Z) (retval_2: Z) ,
  [| (retval <> 0) |]
  &&  (sll retval_2 nil )
  **  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sllb" ->ₛ "head"))
  **  ((( &( "box" ) )) # Ptr  |-> retval)
|--
  [| (0 = 0) |] 
  &&  [| (&((retval)  # "sllb" ->ₛ "head") = &((retval)  # "sllb" ->ₛ "head")) |]
.

Definition nil_list_box_partial_solve_wit_3_aux := 
forall (retval: Z) (retval_2: Z) ,
  [| (retval <> 0) |]
  &&  (sll retval_2 nil )
  **  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sllb" ->ₛ "head"))
|--
  [| (0 = 0) |] 
  &&  [| (&((retval)  # "sllb" ->ₛ "head") = &((retval)  # "sllb" ->ₛ "head")) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> 0)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sllb" ->ₛ "head"))
  **  (sll 0 nil )
.

Definition nil_list_box_partial_solve_wit_3 := nil_list_box_partial_solve_wit_3_pure -> nil_list_box_partial_solve_wit_3_aux.

Definition nil_list_box_which_implies_wit_1 := 
forall (box: Z) (box_head: Z) (box_ptail: Z) ,
  [| (box_head = 0) |] 
  &&  [| (box_ptail = &((box)  # "sllb" ->ₛ "head")) |]
  &&  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> box_head)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> box_ptail)
  **  (sll 0 nil )
|--
  (sllb box nil )
.

(*----- Function cons_list_box -----*)

Definition cons_list_box_return_wit_1 := 
forall (box_pre: Z) (data_pre: Z) (l: (@list Z)) (pt: Z) (retval: Z) ,
  [| (pt = &((box_pre)  # "sllb" ->ₛ "head")) |]
  &&  (sll retval (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sll" ->ₛ "next"))
|--
  (sllb box_pre (cons (data_pre) (l)) )
.

Definition cons_list_box_return_wit_2 := 
forall (box_pre: Z) (data_pre: Z) (l: (@list Z)) (pt: Z) (retval: Z) ,
  [| (pt <> &((box_pre)  # "sllb" ->ₛ "head")) |]
  &&  (sll retval (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  (sllb box_pre (cons (data_pre) (l)) )
.

Definition cons_list_box_partial_solve_wit_1 := 
forall (box_pre: Z) (l: (@list Z)) ,
  (sllb box_pre l )
|--
  (sllb box_pre l )
.

Definition cons_list_box_partial_solve_wit_2 := 
forall (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
|--
  (sll h l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition cons_list_box_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb box l )
|--
  EX (pt: Z)  (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
.

(*----- Function map_list_box -----*)

Definition map_list_box_return_wit_1 := 
forall (x_pre: Z) (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  (sll h (map_mult (x_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  (sllb box_pre (map_mult (x_pre) (l)) )
.

Definition map_list_box_partial_solve_wit_1 := 
forall (box_pre: Z) (l: (@list Z)) ,
  (sllb box_pre l )
|--
  (sllb box_pre l )
.

Definition map_list_box_partial_solve_wit_2 := 
forall (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
|--
  (sll h l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition map_list_box_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb box l )
|--
  EX (pt: Z)  (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
.

(*----- Function free_list_box -----*)

Definition free_list_box_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition free_list_box_partial_solve_wit_1 := 
forall (box_pre: Z) (l: (@list Z)) ,
  (sllb box_pre l )
|--
  (sllb box_pre l )
.

Definition free_list_box_partial_solve_wit_2 := 
forall (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
|--
  (sll h l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition free_list_box_partial_solve_wit_3 := 
forall (box_pre: Z) (pt: Z) (h: Z) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition free_list_box_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb box l )
|--
  EX (pt: Z)  (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
.

(*----- Function app_list_box -----*)

Definition app_list_box_safety_wit_1 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (h1: Z) ,
  ((( &( "b1" ) )) # Ptr  |-> b1_pre)
  **  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  ((( &( "b2" ) )) # Ptr  |-> b2_pre)
  **  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll h2 l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition app_list_box_return_wit_1 := 
forall (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (h2: Z) (pt1: Z) (h1: Z) ,
  [| (h2 = 0) |]
  &&  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll h2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
.

Definition app_list_box_return_wit_2 := 
forall (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (h1: Z) ,
  [| (h2 <> 0) |]
  &&  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll h2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
.

Definition app_list_box_partial_solve_wit_1 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  (sllb b1_pre l1 )
  **  (sllb b2_pre l2 )
|--
  (sllb b1_pre l1 )
  **  (sllb b2_pre l2 )
.

Definition app_list_box_partial_solve_wit_2 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (h1: Z) ,
  [| (h2 <> 0) |]
  &&  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll h2 l2 )
|--
  [| (h2 <> 0) |]
  &&  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll h2 l2 )
.

Definition app_list_box_partial_solve_wit_3 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (h1: Z) ,
  [| (h2 = 0) |]
  &&  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll h2 l2 )
|--
  [| (h2 = 0) |]
  &&  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  ((&((b1_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll h2 l2 )
.

Definition app_list_box_which_implies_wit_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (b1: Z) (b2: Z) ,
  (sllb b1 l1 )
  **  (sllb b2 l2 )
|--
  EX (pt2: Z)  (h2: Z)  (pt1: Z)  (h1: Z) ,
  ((&((b1)  # "sllb" ->ₛ "head")) # Ptr  |-> h1)
  **  ((&((b1)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> 0)
  **  ((&((b2)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll h2 l2 )
.

(*----- Function sll_length -----*)

Definition sll_length_safety_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "len" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  (sll head_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sll_length_entail_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll head_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (0 = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre head_pre l1 )
  **  (sll head_pre l2 )
.

Definition sll_length_entail_wit_2 := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (head_next: Z) (head_data: Z) (l3: (@list Z)) ,
  [| (l2_2 = (cons (head_data) (l3))) |] 
  &&  [| (head <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (len = (Zlength (l1_2))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l3 )
  **  (sllseg head_pre head l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| ((unsigned_last_nbits ((len + 1 )) (32)) = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre head_next l1 )
  **  (sll head_next l2 )
.

Definition sll_length_return_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (head = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (len = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  [| (len = (Zlength (l))) |]
  &&  (sll head_pre l )
.

Definition sll_length_partial_solve_wit_1_pure := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (head <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (len = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "len" ) )) # UInt  |-> len)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  [| (head <> 0) |]
.

Definition sll_length_partial_solve_wit_1_aux := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (head <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (len = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  [| (head <> 0) |] 
  &&  [| (head <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (len = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll head l2 )
  **  (sllseg head_pre head l1 )
.

Definition sll_length_partial_solve_wit_1 := sll_length_partial_solve_wit_1_pure -> sll_length_partial_solve_wit_1_aux.

Definition sll_length_which_implies_wit_1 := 
forall (l2: (@list Z)) (head: Z) ,
  [| (head <> 0) |]
  &&  (sll head l2 )
|--
  EX (head_next: Z)  (head_data: Z)  (l3: (@list Z)) ,
  [| (l2 = (cons (head_data) (l3))) |]
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l3 )
.

(*----- Function sll2array -----*)

Definition sll2array_safety_wit_1 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil retval_2 0 retval )
  **  ((( &( "arr" ) )) # Ptr  |-> retval_2)
  **  (sll head_pre l )
  **  ((( &( "len" ) )) # UInt  |-> retval)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sll2array_safety_wit_2 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (i < len) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (UIntArray.ceil_shape arr 0 (i + 1 ) )
  **  (UIntArray.undef_ceil arr (i + 1 ) len )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "len" ) )) # UInt  |-> len)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sll2array_entail_wit_1 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (UIntArray.undef_ceil retval_2 0 retval )
  **  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (0 = (Zlength (l1))) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre head_pre l1 )
  **  (sll head_pre l2 )
  **  (UIntArray.ceil_shape retval_2 0 0 )
  **  (UIntArray.undef_ceil retval_2 0 retval )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_entail_wit_2 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2_2 = (cons (p_data) (l3))) |] 
  &&  [| (i < len) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (UIntArray.ceil_shape arr 0 (i + 1 ) )
  **  (UIntArray.undef_ceil arr (i + 1 ) len )
  **  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1_2 )
  **  ((out_array_pre) # Ptr  |->_)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| ((i + 1 ) = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre p_next l1 )
  **  (sll p_next l2 )
  **  (UIntArray.ceil_shape arr 0 (i + 1 ) )
  **  (UIntArray.undef_ceil arr (i + 1 ) len )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_return_wit_1 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
  **  ((out_array_pre) # Ptr  |-> arr)
|--
  EX (arr_ret: Z) ,
  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |-> arr_ret)
  **  (UIntArray.full_shape arr_ret (Zlength (l)) )
.

Definition sll2array_partial_solve_wit_1_pure := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "len" ) )) # UInt  |->_)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| ((Zlength (l)) <= INT_MAX) |]
.

Definition sll2array_partial_solve_wit_1_aux := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| ((Zlength (l)) <= INT_MAX) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_partial_solve_wit_1 := sll2array_partial_solve_wit_1_pure -> sll2array_partial_solve_wit_1_aux.

Definition sll2array_partial_solve_wit_2_pure := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |->_)
  **  (sll head_pre l )
  **  ((( &( "len" ) )) # UInt  |-> retval)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (retval = retval) |]
.

Definition sll2array_partial_solve_wit_2_aux := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (retval = retval) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_partial_solve_wit_2 := sll2array_partial_solve_wit_2_pure -> sll2array_partial_solve_wit_2_aux.

Definition sll2array_partial_solve_wit_3_pure := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "len" ) )) # UInt  |-> len)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (l = (app (l1) (l2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (i < len) |]
.

Definition sll2array_partial_solve_wit_3_aux := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (l = (app (l1) (l2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll p l2 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_partial_solve_wit_3 := sll2array_partial_solve_wit_3_pure -> sll2array_partial_solve_wit_3_aux.

Definition sll2array_partial_solve_wit_4 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (i < len) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (i < len) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (len = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (retval = (Zlength (l))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (((arr + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil arr (i + 1 ) len )
  **  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_which_implies_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (p: Z) (i: Z) (len: Z) (arr: Z) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (i < len) |]
  &&  (sll p l2 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
|--
  EX (p_next: Z)  (p_data: Z)  (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (i < len) |]
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.ceil_shape arr 0 i )
  **  (UIntArray.undef_ceil arr i len )
.

(*----- Function sllb2array -----*)

Definition sllb2array_return_wit_1 := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) (arr_ret_2: Z) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll h l )
  **  ((out_array_pre) # Ptr  |-> arr_ret_2)
  **  (UIntArray.full_shape arr_ret_2 (Zlength (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  EX (arr_ret: Z) ,
  (sllb box_pre l )
  **  ((out_array_pre) # Ptr  |-> arr_ret)
  **  (UIntArray.full_shape arr_ret (Zlength (l)) )
.

Definition sllb2array_partial_solve_wit_1 := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllb box_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllb box_pre l )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sllb2array_partial_solve_wit_2_pure := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| ((Zlength (l)) <= INT_MAX) |]
.

Definition sllb2array_partial_solve_wit_2_aux := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  [| ((Zlength (l)) <= INT_MAX) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll h l )
  **  ((out_array_pre) # Ptr  |->_)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition sllb2array_partial_solve_wit_2 := sllb2array_partial_solve_wit_2_pure -> sllb2array_partial_solve_wit_2_aux.

Definition sllb2array_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb box l )
|--
  EX (pt: Z)  (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_project_Strategy_Correct.

Axiom proof_of_nil_list_safety_wit_1 : nil_list_safety_wit_1.
Axiom proof_of_nil_list_return_wit_1 : nil_list_return_wit_1.
Axiom proof_of_cons_list_return_wit_1 : cons_list_return_wit_1.
Axiom proof_of_cons_list_partial_solve_wit_1 : cons_list_partial_solve_wit_1.
Axiom proof_of_free_list_entail_wit_1 : free_list_entail_wit_1.
Axiom proof_of_free_list_entail_wit_2 : free_list_entail_wit_2.
Axiom proof_of_free_list_return_wit_1 : free_list_return_wit_1.
Axiom proof_of_free_list_partial_solve_wit_1_pure : free_list_partial_solve_wit_1_pure.
Axiom proof_of_free_list_partial_solve_wit_1 : free_list_partial_solve_wit_1.
Axiom proof_of_free_list_partial_solve_wit_2 : free_list_partial_solve_wit_2.
Axiom proof_of_free_list_which_implies_wit_1 : free_list_which_implies_wit_1.
Axiom proof_of_map_list_safety_wit_1 : map_list_safety_wit_1.
Axiom proof_of_map_list_entail_wit_1 : map_list_entail_wit_1.
Axiom proof_of_map_list_entail_wit_2 : map_list_entail_wit_2.
Axiom proof_of_map_list_return_wit_1 : map_list_return_wit_1.
Axiom proof_of_map_list_partial_solve_wit_1_pure : map_list_partial_solve_wit_1_pure.
Axiom proof_of_map_list_partial_solve_wit_1 : map_list_partial_solve_wit_1.
Axiom proof_of_map_list_which_implies_wit_1 : map_list_which_implies_wit_1.
Axiom proof_of_nil_list_box_return_wit_1 : nil_list_box_return_wit_1.
Axiom proof_of_nil_list_box_partial_solve_wit_1 : nil_list_box_partial_solve_wit_1.
Axiom proof_of_nil_list_box_partial_solve_wit_2 : nil_list_box_partial_solve_wit_2.
Axiom proof_of_nil_list_box_partial_solve_wit_3_pure : nil_list_box_partial_solve_wit_3_pure.
Axiom proof_of_nil_list_box_partial_solve_wit_3 : nil_list_box_partial_solve_wit_3.
Axiom proof_of_nil_list_box_which_implies_wit_1 : nil_list_box_which_implies_wit_1.
Axiom proof_of_cons_list_box_return_wit_1 : cons_list_box_return_wit_1.
Axiom proof_of_cons_list_box_return_wit_2 : cons_list_box_return_wit_2.
Axiom proof_of_cons_list_box_partial_solve_wit_1 : cons_list_box_partial_solve_wit_1.
Axiom proof_of_cons_list_box_partial_solve_wit_2 : cons_list_box_partial_solve_wit_2.
Axiom proof_of_cons_list_box_which_implies_wit_1 : cons_list_box_which_implies_wit_1.
Axiom proof_of_map_list_box_return_wit_1 : map_list_box_return_wit_1.
Axiom proof_of_map_list_box_partial_solve_wit_1 : map_list_box_partial_solve_wit_1.
Axiom proof_of_map_list_box_partial_solve_wit_2 : map_list_box_partial_solve_wit_2.
Axiom proof_of_map_list_box_which_implies_wit_1 : map_list_box_which_implies_wit_1.
Axiom proof_of_free_list_box_return_wit_1 : free_list_box_return_wit_1.
Axiom proof_of_free_list_box_partial_solve_wit_1 : free_list_box_partial_solve_wit_1.
Axiom proof_of_free_list_box_partial_solve_wit_2 : free_list_box_partial_solve_wit_2.
Axiom proof_of_free_list_box_partial_solve_wit_3 : free_list_box_partial_solve_wit_3.
Axiom proof_of_free_list_box_which_implies_wit_1 : free_list_box_which_implies_wit_1.
Axiom proof_of_app_list_box_safety_wit_1 : app_list_box_safety_wit_1.
Axiom proof_of_app_list_box_return_wit_1 : app_list_box_return_wit_1.
Axiom proof_of_app_list_box_return_wit_2 : app_list_box_return_wit_2.
Axiom proof_of_app_list_box_partial_solve_wit_1 : app_list_box_partial_solve_wit_1.
Axiom proof_of_app_list_box_partial_solve_wit_2 : app_list_box_partial_solve_wit_2.
Axiom proof_of_app_list_box_partial_solve_wit_3 : app_list_box_partial_solve_wit_3.
Axiom proof_of_app_list_box_which_implies_wit_1 : app_list_box_which_implies_wit_1.
Axiom proof_of_sll_length_safety_wit_1 : sll_length_safety_wit_1.
Axiom proof_of_sll_length_entail_wit_1 : sll_length_entail_wit_1.
Axiom proof_of_sll_length_entail_wit_2 : sll_length_entail_wit_2.
Axiom proof_of_sll_length_return_wit_1 : sll_length_return_wit_1.
Axiom proof_of_sll_length_partial_solve_wit_1_pure : sll_length_partial_solve_wit_1_pure.
Axiom proof_of_sll_length_partial_solve_wit_1 : sll_length_partial_solve_wit_1.
Axiom proof_of_sll_length_which_implies_wit_1 : sll_length_which_implies_wit_1.
Axiom proof_of_sll2array_safety_wit_1 : sll2array_safety_wit_1.
Axiom proof_of_sll2array_safety_wit_2 : sll2array_safety_wit_2.
Axiom proof_of_sll2array_entail_wit_1 : sll2array_entail_wit_1.
Axiom proof_of_sll2array_entail_wit_2 : sll2array_entail_wit_2.
Axiom proof_of_sll2array_return_wit_1 : sll2array_return_wit_1.
Axiom proof_of_sll2array_partial_solve_wit_1_pure : sll2array_partial_solve_wit_1_pure.
Axiom proof_of_sll2array_partial_solve_wit_1 : sll2array_partial_solve_wit_1.
Axiom proof_of_sll2array_partial_solve_wit_2_pure : sll2array_partial_solve_wit_2_pure.
Axiom proof_of_sll2array_partial_solve_wit_2 : sll2array_partial_solve_wit_2.
Axiom proof_of_sll2array_partial_solve_wit_3_pure : sll2array_partial_solve_wit_3_pure.
Axiom proof_of_sll2array_partial_solve_wit_3 : sll2array_partial_solve_wit_3.
Axiom proof_of_sll2array_partial_solve_wit_4 : sll2array_partial_solve_wit_4.
Axiom proof_of_sll2array_which_implies_wit_1 : sll2array_which_implies_wit_1.
Axiom proof_of_sllb2array_return_wit_1 : sllb2array_return_wit_1.
Axiom proof_of_sllb2array_partial_solve_wit_1 : sllb2array_partial_solve_wit_1.
Axiom proof_of_sllb2array_partial_solve_wit_2_pure : sllb2array_partial_solve_wit_2_pure.
Axiom proof_of_sllb2array_partial_solve_wit_2 : sllb2array_partial_solve_wit_2.
Axiom proof_of_sllb2array_which_implies_wit_1 : sllb2array_which_implies_wit_1.

End VC_Correct.
