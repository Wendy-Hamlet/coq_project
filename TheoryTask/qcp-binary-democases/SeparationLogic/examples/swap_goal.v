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
Require Import swap_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function swap0 -----*)

Definition swap0_return_wit_1_neq := 
forall (py_pre: Z) (px_pre: Z) (y_neq: Z) (x_neq: Z) ,
  ((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)
|--
  ((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)
.

Definition swap0_return_wit_2_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) ,
  [| (px_pre = py_pre) |]
  &&  ((py_pre) # Int  |-> x_eq)
|--
  ((px_pre) # Int  |-> x_eq)
.

Definition swap0_partial_solve_wit_1_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) ,
  [| (px_pre = py_pre) |]
  &&  ((px_pre) # Int  |-> x_eq)
|--
  [| (px_pre = py_pre) |]
  &&  ((py_pre) # Int  |-> x_eq)
.

Definition swap0_partial_solve_wit_2_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) ,
  [| (px_pre = py_pre) |]
  &&  ((py_pre) # Int  |-> x_eq)
|--
  [| (px_pre = py_pre) |]
  &&  ((px_pre) # Int  |->_)
.

Definition swap0_partial_solve_wit_3_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) ,
  [| (px_pre = py_pre) |]
  &&  ((px_pre) # Int  |-> x_eq)
|--
  [| (px_pre = py_pre) |]
  &&  ((py_pre) # Int  |->_)
.

(*----- Function swap -----*)

Definition swap_entail_wit_1_all := 
forall (py_pre: Z) (px_pre: Z) (para_all: swap_para) ,
  (swap_pre px_pre py_pre para_all )
|--
  (EX (x: Z) ,
  [| (px_pre = py_pre) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((px_pre) # Int  |-> x))
  ||
  (EX (y: Z)  (x_2: Z) ,
  [| (para_all = (swap_neq_para (x_2) (y))) |]
  &&  ((px_pre) # Int  |-> x_2)
  **  ((py_pre) # Int  |-> y))
.

Definition swap_return_wit_1 := 
forall (py_pre: Z) (px_pre: Z) (para_all: swap_para) (x: Z) (y: Z) ,
  [| (para_all = (swap_neq_para (x) (y))) |]
  &&  ((px_pre) # Int  |-> y)
  **  ((py_pre) # Int  |-> x)
|--
  (swap_post px_pre py_pre para_all )
.

Definition swap_return_wit_2 := 
forall (py_pre: Z) (px_pre: Z) (para_all: swap_para) (x: Z) (py: Z) ,
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((py) # Int  |-> x)
|--
  (swap_post px_pre py_pre para_all )
.

Definition swap_partial_solve_wit_1 := 
forall (py_pre: Z) (px_pre: Z) (para_all: swap_para) (x: Z) (py: Z) ,
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((px_pre) # Int  |-> x)
|--
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((py) # Int  |-> x)
.

Definition swap_partial_solve_wit_2 := 
forall (py_pre: Z) (px_pre: Z) (para_all: swap_para) (x: Z) (py: Z) ,
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((py) # Int  |-> x)
|--
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((px_pre) # Int  |->_)
.

Definition swap_partial_solve_wit_3 := 
forall (py_pre: Z) (px_pre: Z) (para_all: swap_para) (x: Z) (py: Z) ,
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((px_pre) # Int  |-> x)
|--
  [| (px_pre = py) |] 
  &&  [| (px_pre = py_pre) |] 
  &&  [| (para_all = (swap_eq_para (x))) |]
  &&  ((py) # Int  |->_)
.

(*----- Function swap_test1 -----*)

Definition swap_test1_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v_2: Z) (y_pre_v_2: Z) ,
  [| (x_pre <> y_pre) |] 
  &&  [| (x_pre_v_2 = 1) |] 
  &&  [| (y_pre_v_2 = 2) |]
  &&  ((x_pre) # Int  |-> y_pre_v_2)
  **  ((y_pre) # Int  |-> x_pre_v_2)
|--
  EX (x_pre_v: Z)  (y_pre_v: Z) ,
  [| (y_pre_v = 1) |] 
  &&  [| (x_pre_v = 2) |]
  &&  ((y_pre) # Int  |-> y_pre_v)
  **  ((x_pre) # Int  |-> x_pre_v)
.

Definition swap_test1_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) (y_pre_v: Z) ,
  [| (x_pre <> y_pre) |] 
  &&  [| (x_pre_v = 1) |] 
  &&  [| (y_pre_v = 2) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
|--
  [| (x_pre <> y_pre) |] 
  &&  [| (x_pre_v = 1) |] 
  &&  [| (y_pre_v = 2) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
.

(*----- Function swap_test2 -----*)

Definition swap_test2_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) ,
  [| (x_pre = y_pre) |] 
  &&  [| (x_pre_v = 1) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
|--
  EX (y_pre_v: Z) ,
  [| (y_pre_v = 1) |]
  &&  ((y_pre) # Int  |-> y_pre_v)
.

Definition swap_test2_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) ,
  [| (x_pre = y_pre) |] 
  &&  [| (x_pre_v = 1) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Int  |-> x_pre_v)
|--
  [| (x_pre = y_pre) |]
.

Definition swap_test2_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) ,
  [| (x_pre = y_pre) |] 
  &&  [| (x_pre_v = 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
|--
  [| (x_pre = y_pre) |] 
  &&  [| (x_pre = y_pre) |] 
  &&  [| (x_pre_v = 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
.

Definition swap_test2_partial_solve_wit_1 := swap_test2_partial_solve_wit_1_pure -> swap_test2_partial_solve_wit_1_aux.

Definition swap_derive_eq_by_all := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) ,
  [| (px_pre = py_pre) |]
  &&  ((px_pre) # Int  |-> x_eq)
|--
EX (para_all: swap_para) ,
  ((swap_pre px_pre py_pre para_all ))
  **
  (((swap_post px_pre py_pre para_all ))
  -*
  (((py_pre) # Int  |-> x_eq)))
.

Definition swap_derive_neq_by_all := 
forall (py_pre: Z) (px_pre: Z) (y_neq: Z) (x_neq: Z) ,
  ((px_pre) # Int  |-> x_neq)
  **  ((py_pre) # Int  |-> y_neq)
|--
EX (para_all: swap_para) ,
  ((swap_pre px_pre py_pre para_all ))
  **
  (((swap_post px_pre py_pre para_all ))
  -*
  (((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)))
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_swap0_return_wit_1_neq : swap0_return_wit_1_neq.
Axiom proof_of_swap0_return_wit_2_eq : swap0_return_wit_2_eq.
Axiom proof_of_swap0_partial_solve_wit_1_eq : swap0_partial_solve_wit_1_eq.
Axiom proof_of_swap0_partial_solve_wit_2_eq : swap0_partial_solve_wit_2_eq.
Axiom proof_of_swap0_partial_solve_wit_3_eq : swap0_partial_solve_wit_3_eq.
Axiom proof_of_swap_entail_wit_1_all : swap_entail_wit_1_all.
Axiom proof_of_swap_return_wit_1 : swap_return_wit_1.
Axiom proof_of_swap_return_wit_2 : swap_return_wit_2.
Axiom proof_of_swap_partial_solve_wit_1 : swap_partial_solve_wit_1.
Axiom proof_of_swap_partial_solve_wit_2 : swap_partial_solve_wit_2.
Axiom proof_of_swap_partial_solve_wit_3 : swap_partial_solve_wit_3.
Axiom proof_of_swap_test1_return_wit_1 : swap_test1_return_wit_1.
Axiom proof_of_swap_test1_partial_solve_wit_1 : swap_test1_partial_solve_wit_1.
Axiom proof_of_swap_test2_return_wit_1 : swap_test2_return_wit_1.
Axiom proof_of_swap_test2_partial_solve_wit_1_pure : swap_test2_partial_solve_wit_1_pure.
Axiom proof_of_swap_test2_partial_solve_wit_1 : swap_test2_partial_solve_wit_1.
Axiom proof_of_swap_derive_eq_by_all : swap_derive_eq_by_all.
Axiom proof_of_swap_derive_neq_by_all : swap_derive_neq_by_all.

End VC_Correct.
