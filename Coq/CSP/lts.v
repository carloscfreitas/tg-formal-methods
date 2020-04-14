Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.
Require Import semantics_sos.

(** LTS RELATION **)

Inductive transitionR : specification -> (proc_body * event_tau_tick * proc_body) -> proc_body -> Prop :=
  | transition_rule (C : specification) (P' : proc_body) (a : event_tau_tick) (Q : proc_body)
    (P : proc_body)  (Tc : list event_tau_tick) :
      (C # P /// Tc ==> P') ->
      (C # P' // a ==> Q) ->
      transitionR C (P', a, Q) P.

Local Open Scope string.

Definition TOY_PROBLEM := Spec [Channel {{"a", "b"}}] ["P" ::= "a" --> "b" --> STOP].

Example test1 : transitionR TOY_PROBLEM ("a" --> "b" --> STOP, Event "a", "b" --> STOP) ("a" --> "b" --> STOP).
Proof.
  apply transition_rule with (Tc := nil).
  - apply sos_empty_rule.
  - apply prefix_rule.
Qed.

Example test2 : transitionR TOY_PROBLEM ("b" --> STOP, Event "b", STOP) ("a" --> "b" --> STOP).
Proof.
  apply transition_rule with (Tc := [Event "a"]).
  - apply sos_transitive_rule with (R := "b" --> STOP).
    * apply prefix_rule.
    * apply sos_empty_rule.
  - apply prefix_rule.
Qed.

Inductive transitionsR : specification -> list (proc_body * event_tau_tick * proc_body) -> proc_body -> Prop :=
  | transitions_empty_rule (C : specification) (P : proc_body) :
      transitionsR C nil P
  | transitions_rule (C : specification) (P : proc_body) (head : proc_body * event_tau_tick * proc_body)
    (tail : list (proc_body * event_tau_tick * proc_body)) :
      transitionR C head P ->
      transitionsR C tail P ->
      transitionsR C (head :: tail) P.

Example test3 :
  transitionsR
    TOY_PROBLEM 
    [
      ("b" --> STOP, Event "b", STOP)
      ; ("a" --> "b" --> STOP, Event "a", "b" --> STOP)
    ] 
    ("a" --> "b" --> STOP).
Proof.
  apply transitions_rule.
  - apply transition_rule with (Tc := [Event "a"]).
    * apply sos_transitive_rule with (R := "b" --> STOP).
      + apply prefix_rule.
      + apply sos_empty_rule.
    * apply prefix_rule.
  - apply transitions_rule.
    * apply transition_rule with (Tc := nil).
      + apply sos_empty_rule.
      + apply prefix_rule.
    * apply transitions_empty_rule.
Qed.

Inductive ltsR (C : specification) (T : list (proc_body * event_tau_tick * proc_body)) (P : proc_body) : Prop :=
  | lts_rule :
      (forall (t : proc_body * event_tau_tick * proc_body), transitionR C t P -> In t T) ->
      transitionsR C T P ->
      ltsR C T P.

Example lts1 :
  ltsR TOY_PROBLEM
    [
      ("b" --> STOP, Event "b", STOP)
      ; ("a" --> "b" --> STOP, Event "a", "b" --> STOP)
    ]
    ("a" --> "b" --> STOP).
Proof.
    apply lts_rule.
    - intros. inversion H. subst.
      inversion H0. subst.
      + inversion H1. subst.
        * simpl. right. left. reflexivity.
        * subst. inversion H2.
      + subst. inversion H2. subst.
        inversion H3. subst. inversion H1. subst.
        * simpl. left. reflexivity.
        * subst. inversion H4.
        * subst. inversion H4. subst. inversion H5. subst.
          inversion H1. subst. inversion H6. subst.
          inversion H6. subst. inversion H8. subst. inversion H6.
        * subst. inversion H4.
    - apply transitions_rule.
      + apply transition_rule with (Tc := [Event "a"]).
        * apply sos_transitive_rule with (R := "b" --> STOP).
          { apply prefix_rule. }
          { apply sos_empty_rule. }
        * apply prefix_rule.
      + apply transitions_rule.
        * apply transition_rule with (Tc := nil).
          { apply sos_empty_rule. }
          { apply prefix_rule. }
        * apply transitions_empty_rule.
Qed.

Theorem event_tau_tick_eq_dec :
  forall (e1 e2 : event_tau_tick),
    {e1 = e2} + {e1 <> e2}.
Proof.
  intros. destruct e1, e2 ; try (left ; reflexivity) ;
  try (right ; unfold not ; intros H ; now inversion H).
  decide equality ; apply event_dec.
Qed.

Theorem alphabet_eq_dec :
  forall (a1 a2 : alphabet),
    {a1 = a2} + {a1 <> a2}.
Proof.
  intros. destruct a1, a2.
  repeat (decide equality ; try apply event_dec).
Qed.

Theorem proc_body_eq_dec :
  forall (p1 p2 : proc_body),
    {p1 = p2} + {p1 <> p2}.
Proof.
  intros. destruct p1, p2 ;
    try (right ; unfold not ; intros H ; now inversion H) ;
    try (left ; reflexivity) ;
    decide equality ; try apply event_dec ; try apply alphabet_eq_dec.
Qed.

Theorem transition_eq_dec :
  forall (t1 t2 : (proc_body * event_tau_tick * proc_body)),
    {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality.
  - decide equality ; try apply event_dec ; try apply alphabet_eq_dec.
  - decide equality ; try apply event_tau_tick_eq_dec ; try apply proc_body_eq_dec.
Qed.

Fixpoint get_target_states (T : set (proc_body * event_tau_tick * proc_body)) : (set proc_body) :=
  match T with
  | nil              => nil
  | (p,a,p') :: tail => set_add proc_body_eq_dec p' (get_target_states tail)
  end.

Inductive ltsR' : specification -> set (proc_body * event_tau_tick * proc_body) -> set proc_body -> Prop :=
  | lts_empty_rule (C : specification) (S : set proc_body) (P : proc_body) :
    Datatypes.length S = 1 ->
    In P S ->
    ~ (exists (a : event_tau_tick) (P' : proc_body), C # P // a ==> P') ->
    ltsR' C nil S
  | lts_inductive_rule (C : specification) (T T' T'' : set (proc_body * event_tau_tick * proc_body)) (P : proc_body) (L L' : set proc_body) :
    In P L ->
    (forall (a : event_tau_tick) (P' : proc_body), (C # P // a ==> P') <-> In (P,a,P') T') ->
    L' = get_target_states T' ->
    ltsR' C T'' L' ->
    T = (set_union transition_eq_dec T' T'') ->
    ltsR' C T L.

Example lts1' :
  ltsR'
    (* context *)
    TOY_PROBLEM (* context *)
    (* LTS *)
    [ ("a" --> "b" --> STOP, Event "a", "b" --> STOP) ;
      ("b" --> STOP, Event "b", STOP) ]
    (* INITIAL STATE *)
    ["a" --> "b" --> STOP].
Proof.
  eapply lts_inductive_rule with
    (T' := [("a" --> "b" --> STOP, Event "a", "b" --> STOP)]).
  - simpl. left. reflexivity.
  - intros. split.
    + intros. inversion H. subst.
      * simpl. left. reflexivity.
      * subst. inversion H0.
    + intros. simpl in H. destruct H.
      * inversion H. subst. apply prefix_rule.
      * inversion H.
  - reflexivity.
  - eapply lts_inductive_rule with
    (T' := [("b" --> STOP, Event "b", STOP)])
    (L' := [STOP]).
    + simpl. left. reflexivity.
    + intros. split.
      * intros. inversion H. subst.
        { simpl. left. reflexivity. }
        { subst. inversion H0. }
      * intros. simpl in H. destruct H.
        { inversion H. subst. apply prefix_rule. }
        { inversion H. }
    + simpl. reflexivity.
    + eapply lts_empty_rule.
      * simpl. reflexivity.
      * simpl. left. reflexivity.
      * unfold not. intros. destruct H. destruct H.
        inversion H. subst. inversion H0.
    + simpl. reflexivity.
  - simpl.
    destruct (transition_eq_dec ("b" --> STOP, Event "b", STOP)
                                ("a" --> "b" --> STOP, Event "a", "b" --> STOP)).
    + inversion e.
    + reflexivity.
Qed.

Definition TOY_PROBLEM' := Spec
  [Channel {{"a", "b", "c"}}]
  ["P" ::= ("a" --> "b" --> STOP) [] ("c" --> STOP)].

Example lts2' :
  ltsR'
    (* context *)
    TOY_PROBLEM (* context *)
    (* LTS *)
    [ (("a" --> "b" --> STOP) [] ("c" --> STOP), Event "a", "b" --> STOP);
      (("a" --> "b" --> STOP) [] ("c" --> STOP), Event "c", STOP);
      ("b" --> STOP, Event "b", STOP) ]
    (* INITIAL STATE *)
    [("a" --> "b" --> STOP) [] ("c" --> STOP)].
Proof.
  eapply lts_inductive_rule with
    (T' :=
      [(("a" --> "b" --> STOP) [] ("c" --> STOP), Event "a", "b" --> STOP);
       (("a" --> "b" --> STOP) [] ("c" --> STOP), Event "c", STOP)]).
  - simpl. left. reflexivity.
  - intros. split.
    + intros. inversion H. subst.
      * inversion H0.
      * subst. inversion H6. subst.
        { simpl. left. reflexivity. }
        { subst. inversion H0. }
      * subst. inversion H6. subst.
        { simpl. right. left. reflexivity. }
        { subst. inversion H0. }
      * subst. inversion H5. subst. inversion H0.
      * subst. inversion H5. subst. inversion H0.
    + intros. simpl in H. destruct H.
      * inversion H. apply ext_choice_left_rule.
        { unfold not. intros. subst. inversion H0. }
        { apply prefix_rule. }
      * destruct H.
        { inversion H. apply ext_choice_right_rule.
          { unfold not. intros. subst. inversion H0. }
          { apply prefix_rule. }
        }
        { inversion H. }
  - reflexivity.
  - simpl. destruct (proc_body_eq_dec ("b" --> STOP) (STOP)) eqn:H.
    + inversion e.
    + eapply lts_inductive_rule with
        (T' := [(("b" --> STOP), Event "b", STOP)]).
      * simpl. right. left. reflexivity.
      * intros. split.
        { intros. inversion H0. subst.
          { simpl. left. reflexivity. }
          { subst. inversion H1. }
        }
        { intros. simpl in H0. destruct H0.
          { inversion H0. apply prefix_rule. }
          { inversion H0. }
        }
      * simpl. reflexivity.
      * eapply lts_empty_rule.
        { simpl. reflexivity. }
        { simpl. left. reflexivity. }
        { unfold not. intros. destruct H0. destruct H0.
          inversion H0. subst. inversion H1. }
      * simpl. reflexivity.
  - simpl.
    destruct (transition_eq_dec
      ("b" --> STOP, Event "b", STOP)
      ("a" --> "b" --> STOP [] "c" --> STOP, Event "a", "b" --> STOP)).
    + inversion e.
    + destruct (transition_eq_dec
        ("b" --> STOP, Event "b", STOP)
        ("a" --> "b" --> STOP [] "c" --> STOP, Event "c", STOP)).
      * inversion e.
      * reflexivity.
Qed.

Local Close Scope string.