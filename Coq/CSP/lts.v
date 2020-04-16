Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.
Require Import semantics_sos.

(** LTS RELATION **)

Definition transition := prod (prod proc_body event_tau_tick) proc_body.

Theorem transition_eq_dec :
  forall (t1 t2 : transition),
    {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality.
  - decide equality ; try apply event_dec ; try apply alphabet_eq_dec.
  - decide equality ; try apply event_tau_tick_eq_dec ; try apply proc_body_eq_dec.
Defined.

Fixpoint target_proc_bodies (T : set transition) : set proc_body :=
  match T with
  | nil              => nil
  | (_, _, P') :: tl => set_add proc_body_eq_dec P' (target_proc_bodies tl)
  end.
  
Fixpoint transitions_from_P (P : proc_body) (T : set transition) : set transition :=
  match T with
  | nil                => nil
  | (P', e, P'') :: tl => if proc_body_eq_dec P P'
                          then set_add transition_eq_dec (P',e,P'')
                                                         (transitions_from_P P tl)
                          else transitions_from_P P tl
  end.
  
Inductive ltsR' :
  specification -> (* the context *)
  set transition -> (* the transitions of the LTS *)
  set proc_body -> (* the states still to be visited *)
  set proc_body -> (* the visited states *)
  Prop :=
  | lts_empty_rule (C : specification) (visited : set proc_body) :
      ltsR' C nil nil visited
  | lts_inductive_rule
        (C : specification)
        (T : set transition)
        (P : proc_body)
        (tl visited : set proc_body) :
      let T' := transitions_from_P P T in
      let T'' := set_diff transition_eq_dec T T' in
      let visited' := set_add proc_body_eq_dec P visited in
      let to_visit := set_diff proc_body_eq_dec
                        (set_union proc_body_eq_dec tl (target_proc_bodies T'))
                        visited' in
      (forall (a : event_tau_tick) (P' : proc_body),
         (C # P // a ==> P') <-> In (P,a,P') T') ->
      ltsR' C T'' to_visit visited' ->
      ltsR' C T (P :: tl) visited.

Definition ltsR (C : specification) (T : set transition) (name : string) : Prop :=
  NoDup T /\ ltsR' C T [get_proc_body C name] nil.

Local Open Scope string.
Definition TOY_PROBLEM := Spec [Channel {{"a", "b"}}] ["P" ::= "a" --> "b" --> STOP].

Example lts1' :
  ltsR
    (* context *)
    TOY_PROBLEM (* context *)
    (* LTS *)
    [ ("a" --> "b" --> STOP, Event "a", "b" --> STOP) ;
      ("b" --> STOP, Event "b", STOP) ]
    (* PROCESS NAME *)
    "P".
Proof.
  unfold ltsR. split.
  - repeat (
        apply NoDup_cons ;
        try (unfold not ; intros H ; inversion H ; inversion H0)
    ) ; apply NoDup_nil.
  - simpl. apply lts_inductive_rule.
    + intros. split.
      * intros. inversion H ; subst.
        { simpl. left. reflexivity. }
        { inversion H0. }
      * intros. inversion H ; subst.
        { inversion H0. subst. apply prefix_rule. }
        { inversion H0. }
    + simpl. apply lts_inductive_rule.
      * intros. split.
        { intros. inversion H ; subst.
          { simpl. left. reflexivity. }
          { inversion H0. }
        }
        { intros. inversion H ; subst.
          { inversion H0. subst. apply prefix_rule. }
          { inversion H0. }
        } 
      * simpl. apply lts_inductive_rule.
        { intros. split.
          { intros. inversion H. subst. inversion H0. }
          { intros. inversion H. }
        }
        { simpl. apply lts_empty_rule. }
Qed.

(* TODO: update the following proofs considering
   the new formulation of ltsR. *)

(**
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
**)

Local Close Scope string.