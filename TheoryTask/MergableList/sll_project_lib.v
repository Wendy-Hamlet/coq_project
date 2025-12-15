Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX y: addr,
                   &(x # "sll" ->ₛ "data") # Int |-> a **
                   &(x # "sll" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

Fixpoint sllseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = y |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX z: addr,
                   &(x # "sll" ->ₛ "data") # Int |-> a **
                   &(x # "sll" ->ₛ "next") # Ptr |-> z **
                   sllseg z y l0
  end.

Definition map_mult (x: Z) (l: list Z): list Z :=
  List.map (fun a => x * a) l.

