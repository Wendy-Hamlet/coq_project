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

(*----- Function exgcd -----*)

Definition exgcd_safety_wit_1_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_2_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_3_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition exgcd_safety_wit_4_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exgcd_safety_wit_5_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_6_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_7_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exgcd_safety_wit_8_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_9_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_10_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_11_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_safety_wit_12_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) |]
.

Definition exgcd_safety_wit_13_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) |]
.

Definition exgcd_safety_wit_14_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_safety_wit_15_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_callee_v = 0) |] 
  &&  [| ((Zabs (y_callee_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) |]
.

Definition exgcd_safety_wit_16_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_callee_v = 0) |] 
  &&  [| ((Zabs (y_callee_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) |]
.

Definition exgcd_safety_wit_17_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_callee_v = 0) |] 
  &&  [| ((Zabs (y_callee_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_safety_wit_18_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= 1) |] 
  &&  [| (y_callee_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) )) |]
.

Definition exgcd_safety_wit_19_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= 1) |] 
  &&  [| (y_callee_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre ÷ b_pre ) * y_callee_v ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_callee_v )) |]
.

Definition exgcd_safety_wit_20_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= 1) |] 
  &&  [| (y_callee_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_callee_v)
  **  ((x_pre) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_return_wit_1_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (a_pre))) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  (EX (y_pre_v: Z)  (x_pre_v: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_2_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (a_pre))) |] 
  &&  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  (EX (y_pre_v: Z)  (x_pre_v: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_3_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (a_pre))) |] 
  &&  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  (EX (y_pre_v: Z)  (x_pre_v: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_4_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= 1) |] 
  &&  [| (y_callee_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))
  **  ((x_pre) # Int  |-> y_callee_v)
|--
  (EX (y_pre_v: Z)  (x_pre_v: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_5_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_callee_v = 0) |] 
  &&  [| ((Zabs (y_callee_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))
  **  ((x_pre) # Int  |-> y_callee_v)
|--
  (EX (y_pre_v: Z)  (x_pre_v: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_6_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_callee_v ) + ((a_pre % ( b_pre ) ) * y_callee_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> (x_callee_v - ((a_pre ÷ b_pre ) * y_callee_v ) ))
  **  ((x_pre) # Int  |-> y_callee_v)
|--
  (EX (y_pre_v: Z)  (x_pre_v: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX (y_pre_v_2: Z)  (x_pre_v_2: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX (y_pre_v_3: Z)  (x_pre_v_3: Z) ,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_partial_solve_wit_1_Proof_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |]
.

Definition exgcd_partial_solve_wit_1_Proof_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_1_Proof := exgcd_partial_solve_wit_1_Proof_pure -> exgcd_partial_solve_wit_1_Proof_aux.

Definition exgcd_partial_solve_wit_2_Proof_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |]
.

Definition exgcd_partial_solve_wit_2_Proof_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_2_Proof := exgcd_partial_solve_wit_2_Proof_pure -> exgcd_partial_solve_wit_2_Proof_aux.

Definition exgcd_partial_solve_wit_3_Proof_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |]
.

Definition exgcd_partial_solve_wit_3_Proof_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_3_Proof := exgcd_partial_solve_wit_3_Proof_pure -> exgcd_partial_solve_wit_3_Proof_aux.

Definition exgcd_partial_solve_wit_4_Proof_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| ((a_pre % ( b_pre ) ) <= INT_MAX) |] 
  &&  [| (INT_MIN < (a_pre % ( b_pre ) )) |]
.

Definition exgcd_partial_solve_wit_4_Proof_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| ((a_pre % ( b_pre ) ) <= INT_MAX) |] 
  &&  [| (INT_MIN < (a_pre % ( b_pre ) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |->_)
  **  ((x_pre) # Int  |->_)
.

Definition exgcd_partial_solve_wit_4_Proof := exgcd_partial_solve_wit_4_Proof_pure -> exgcd_partial_solve_wit_4_Proof_aux.

Definition exgcd_derive_Inter_by_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  ([| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_))
  **
  (((EX y_callee_v x_callee_v retval_2,
  [| (retval_2 = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_callee_v ) + (b_pre * y_callee_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_callee_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_callee_v)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_callee_v)
  **  ((y_pre) # Int  |-> y_callee_v))
  ||
  (EX y_callee_v_2 x_callee_v_2 retval_2,
  [| (retval_2 = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_callee_v_2 ) + (b_pre * y_callee_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_callee_v_2 = 0) |] 
  &&  [| ((Zabs (y_callee_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_callee_v_2)
  **  ((y_pre) # Int  |-> y_callee_v_2))
  ||
  (EX y_callee_v_3 x_callee_v_3 retval_2,
  [| (retval_2 = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_callee_v_3 ) + (b_pre * y_callee_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_callee_v_3)) <= 1) |] 
  &&  [| (y_callee_v_3 = 0) |]
  &&  ((x_pre) # Int  |-> x_callee_v_3)
  **  ((y_pre) # Int  |-> y_callee_v_3)))
  -*
  (EX y_pre_v x_pre_v retval,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)))
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_exgcd_safety_wit_1_Proof : exgcd_safety_wit_1_Proof.
Axiom proof_of_exgcd_safety_wit_2_Proof : exgcd_safety_wit_2_Proof.
Axiom proof_of_exgcd_safety_wit_3_Proof : exgcd_safety_wit_3_Proof.
Axiom proof_of_exgcd_safety_wit_4_Proof : exgcd_safety_wit_4_Proof.
Axiom proof_of_exgcd_safety_wit_5_Proof : exgcd_safety_wit_5_Proof.
Axiom proof_of_exgcd_safety_wit_6_Proof : exgcd_safety_wit_6_Proof.
Axiom proof_of_exgcd_safety_wit_7_Proof : exgcd_safety_wit_7_Proof.
Axiom proof_of_exgcd_safety_wit_8_Proof : exgcd_safety_wit_8_Proof.
Axiom proof_of_exgcd_safety_wit_9_Proof : exgcd_safety_wit_9_Proof.
Axiom proof_of_exgcd_safety_wit_10_Proof : exgcd_safety_wit_10_Proof.
Axiom proof_of_exgcd_safety_wit_11_Proof : exgcd_safety_wit_11_Proof.
Axiom proof_of_exgcd_safety_wit_12_Proof : exgcd_safety_wit_12_Proof.
Axiom proof_of_exgcd_safety_wit_13_Proof : exgcd_safety_wit_13_Proof.
Axiom proof_of_exgcd_safety_wit_14_Proof : exgcd_safety_wit_14_Proof.
Axiom proof_of_exgcd_safety_wit_15_Proof : exgcd_safety_wit_15_Proof.
Axiom proof_of_exgcd_safety_wit_16_Proof : exgcd_safety_wit_16_Proof.
Axiom proof_of_exgcd_safety_wit_17_Proof : exgcd_safety_wit_17_Proof.
Axiom proof_of_exgcd_safety_wit_18_Proof : exgcd_safety_wit_18_Proof.
Axiom proof_of_exgcd_safety_wit_19_Proof : exgcd_safety_wit_19_Proof.
Axiom proof_of_exgcd_safety_wit_20_Proof : exgcd_safety_wit_20_Proof.
Axiom proof_of_exgcd_return_wit_1_Proof : exgcd_return_wit_1_Proof.
Axiom proof_of_exgcd_return_wit_2_Proof : exgcd_return_wit_2_Proof.
Axiom proof_of_exgcd_return_wit_3_Proof : exgcd_return_wit_3_Proof.
Axiom proof_of_exgcd_return_wit_4_Proof : exgcd_return_wit_4_Proof.
Axiom proof_of_exgcd_return_wit_5_Proof : exgcd_return_wit_5_Proof.
Axiom proof_of_exgcd_return_wit_6_Proof : exgcd_return_wit_6_Proof.
Axiom proof_of_exgcd_partial_solve_wit_1_Proof_pure : exgcd_partial_solve_wit_1_Proof_pure.
Axiom proof_of_exgcd_partial_solve_wit_1_Proof : exgcd_partial_solve_wit_1_Proof.
Axiom proof_of_exgcd_partial_solve_wit_2_Proof_pure : exgcd_partial_solve_wit_2_Proof_pure.
Axiom proof_of_exgcd_partial_solve_wit_2_Proof : exgcd_partial_solve_wit_2_Proof.
Axiom proof_of_exgcd_partial_solve_wit_3_Proof_pure : exgcd_partial_solve_wit_3_Proof_pure.
Axiom proof_of_exgcd_partial_solve_wit_3_Proof : exgcd_partial_solve_wit_3_Proof.
Axiom proof_of_exgcd_partial_solve_wit_4_Proof_pure : exgcd_partial_solve_wit_4_Proof_pure.
Axiom proof_of_exgcd_partial_solve_wit_4_Proof : exgcd_partial_solve_wit_4_Proof.
Axiom proof_of_exgcd_derive_Inter_by_Proof : exgcd_derive_Inter_by_Proof.

End VC_Correct.
