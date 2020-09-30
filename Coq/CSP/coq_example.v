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