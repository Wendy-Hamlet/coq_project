From Coq Require Import Bool List.
Import ListNotations.
Require Import AUXLib.EqDec.


(** Wrap [Lists.List.remove] using [EqDec] *)
Definition remove_eqdec {A: Type} {eqd: EqDec A eq} := @remove A equiv_dec.

(** Define a more readable version of deciding membership in a list *)
Fixpoint inb {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | y :: ys => (x ==b y) || (inb x ys)
  end.

Lemma inb_true_iff {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) :
  inb x l = true <-> List.In x l.
Proof.
  induction l; simpl.
  - split; [congruence|tauto].
  - split.
    + destruct (_ ==b _) eqn:H1; simpl; intros H; [left|right].
      * apply equiv_decb_true_eq in H1. auto.
      * apply IHl. auto.
    + intros H. destruct H.
      * apply eq_sym in H. apply eq_equiv_decb_true in H.
        rewrite H. reflexivity.
      * destruct (_ ==b _); simpl; auto. apply IHl. auto.
Defined.

Lemma inb_false_iff {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) :
  inb x l = false <-> ~ List.In x l.
Proof.
  transitivity (~ inb x l = true).
  { generalize (inb x l). intros b. destruct b; split; auto; congruence. }
  apply not_iff_compat. apply inb_true_iff.
Qed.

Definition In_dec {A: Type} {eqd: EqDec A eq} (x: A) (l: list A)
    : {List.In x l} + {~ List.In x l} :=
  match inb x l as b return (inb x l = b -> _) with
  | true => fun H => left (proj1 (inb_true_iff x l) H)
  | false => fun H => right (proj1 (inb_false_iff x l) H)
  end eq_refl.



(** Transparent version of incl_dec *)
Definition incl_dec {A} (l1 l2 : list A) {dec : EqDec A eq} :
    {incl l1 l2} + {~ incl l1 l2}.
Proof.
  destruct (forallb (fun x => inb x l2) l1) eqn:H.
  - left. intros x Hx. rewrite forallb_forall in H.
    specialize (H x Hx). apply inb_true_iff in H. apply H.
  - right. intros Hincl. eapply eq_true_false_abs. 2: apply H.
    apply forallb_forall. intros x Hx. specialize (Hincl x Hx).
    apply inb_true_iff. apply Hincl.
Defined.

(** Transparent version of NoDup_dec *)
Definition NoDup_dec {A} (l : list A) {dec : EqDec A eq} :
    {NoDup l} + {~ NoDup l}.
Proof.
  induction l as [|x xs IH].
  - left. constructor.
  - destruct IH as [Hndup | Hndup].
    + destruct (In_dec x xs) as [Hin | Hnin].
      * right. intros H. inversion_clear H. tauto.
      * left. constructor; auto.
    + right. intros H. inversion_clear H. tauto.
Defined.
