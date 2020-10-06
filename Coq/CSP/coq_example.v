Module NatPlaygroud.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.
End NatPlaygroud.

Require Import Coq.Init.Nat.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_minus2 : forall n:nat,
  ev n -> ev (pred (pred n)).
Proof.
  intros.
  destruct H.
  - simpl. apply ev_0.
  - simpl. apply H.
Qed.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Require Import Lists.List.
Import ListNotations.

Example elem_not_in_list : ~ (In 4 [0 ; 1 ; 2 ; 3]).
Proof.
  unfold not. simpl. intros.
  destruct H.
  - inversion H.
  - destruct H.
    * inversion H.
    * destruct H.
      + inversion H.
      + destruct H.
        { inversion H. }
        { contradiction. }
Qed.

Ltac solve_not_in := unfold not;
  let H := fresh "H" in (
    intros H; repeat (contradiction + (destruct H; [> inversion H | ]))
  ).

Example elem_not_in_list' : ~ (In 4 [0 ; 1 ; 2 ; 3]).
Proof. solve_not_in. Qed.

Lemma negb_involutive : forall (b : bool),
  negb (negb b) = b.
Proof.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. simpl in IHn. rewrite IHn.
    rewrite negb_involutive. reflexivity.
Qed.

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import List ZArith. Import ListNotations.

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if h =? x then t else h :: remove x t
  end.

Conjecture removeP : forall x l,  ~ (In x (remove x l)).

QuickChick removeP.