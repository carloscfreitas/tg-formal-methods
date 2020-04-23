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
  match get_proc_body C name with
  | Some body => NoDup T /\ ltsR' C T [body] nil
  | None => False
  end.

Local Open Scope string.
Definition TOY_PROBLEM := Spec [Channel {{"a", "b"}}] ["P" ::= "a" --> "b" --> STOP].

Example lts1 :
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

Definition TOY_PROBLEM' := Spec
  [Channel {{"a", "b", "c"}}]
  ["P" ::= ("a" --> "b" --> STOP) [] ("c" --> STOP)].

Example lts2 :
  ltsR
    (* context *)
    TOY_PROBLEM' (* context *)
    (* LTS *)
    [ (("a" --> "b" --> STOP) [] ("c" --> STOP), Event "a", "b" --> STOP);
      (("a" --> "b" --> STOP) [] ("c" --> STOP), Event "c", STOP);
      ("b" --> STOP, Event "b", STOP) ]
    (* INITIAL STATE *)
    "P".
Proof.
  unfold ltsR. split.
  - apply NoDup_cons.
    + unfold not. intros. inversion H. inversion H0.
      inversion H0. inversion H1. inversion H1.
    + apply NoDup_cons.
      * unfold not. simpl. intros. destruct H.
        inversion H. inversion H.
      * apply NoDup_cons.
        { unfold not. intros. inversion H. }
        { apply NoDup_nil. }
  - apply lts_inductive_rule.
    + intros. split.
      * intros. simpl in H. inversion H ; subst.
        inversion H0 ; subst. inversion H6 ; subst.
        { simpl. right. left. reflexivity. }
        { contradiction. }
        inversion H6 ; subst.
        { simpl. left. reflexivity. }
        { contradiction. }
        inversion H5 ; subst. inversion H0.
        inversion H5 ; subst. inversion H0.
      * intros. simpl. simpl in H. inversion H.
        { inversion H0 ; subst. apply ext_choice_right_rule.
          { unfold not. intros. inversion H1. }
          { apply prefix_rule. }
        }
        { inversion H0 ; subst. inversion H1 ; subst.
          { apply ext_choice_left_rule.
            { unfold not. intros. inversion H2. }
            { apply prefix_rule. }
          }
          { contradiction. }
        }
    + simpl. apply lts_inductive_rule.
      * intros. split.
        { intros. inversion H ; subst.
          { simpl. left. reflexivity. }
          { inversion H0. }
        }
        { intros. simpl in H. inversion H.
          { inversion H0 ; subst. apply prefix_rule. }
          { contradiction. }
        }
      * simpl. apply lts_inductive_rule.
        { intros. split.
          { intros. inversion H ; subst. inversion H0. }
          { intros. inversion H. }
        }
        { simpl. apply lts_empty_rule. }
Qed.

Definition P := "P" ::= "P".
Definition UNDERDEFINED_RECURSION := Spec [Channel {{}}] [P].

Example lts3 : ltsR UNDERDEFINED_RECURSION [(ProcRef "P", Tau, ProcRef "P")] "P".
Proof.
  unfold ltsR. split.
  - repeat (
      apply NoDup_cons ;
      try (unfold not ; intros H ; inversion H ; inversion H0)
    ) ; apply NoDup_nil.
  - simpl. apply lts_inductive_rule.
    + intros. split.
      * intros. inversion H ; subst.
        inversion H0 ; subst. simpl in H.
        simpl. left. inversion H1. reflexivity.
      * intros. inversion H.
        { inversion H0 ; subst. apply reference_rule with (name := "P").
          { reflexivity. }
          { reflexivity. }
        }
        { inversion H0. }
    + simpl. apply lts_empty_rule.
Qed.

Definition S_LIGHT := Spec [Channel {{"on", "off"}}] ["LIGHT" ::= "on" --> "off" --> "LIGHT"].
Example lts4 :
  ltsR
    S_LIGHT
    [
      ("on" --> "off" --> "LIGHT", Event "on", "off" --> "LIGHT") ; 
      ("off" --> "LIGHT", Event "off", ProcRef "LIGHT") ;
      (ProcRef "LIGHT", Tau, "on" --> "off" --> "LIGHT")
    ]
    "LIGHT".
Proof.
  unfold ltsR. split.
  - repeat (
      apply NoDup_cons ;
      try (unfold not ; intros H ; inversion H ; inversion H0)
    ). inversion H1. inversion H1. apply NoDup_nil.
  - apply lts_inductive_rule.
    * split.
      + simpl. intros. inversion H ; subst.
        { left. reflexivity. }
        { inversion H0. }
      + simpl. intros. inversion H ; subst. inversion H0 ; subst.
        { apply prefix_rule. }
        { inversion H0. }
    * simpl. apply lts_inductive_rule.
      + split.
        {
          intros. simpl. inversion H ; subst.
          { left. reflexivity. }
          { inversion H0. }
        }
        {
          simpl. intros. inversion H ; subst. inversion H0 ; subst.
          { apply prefix_rule. }
          { inversion H0. }
        }
      + simpl. apply lts_inductive_rule.
        {
          split.
          {
            simpl. intros. inversion H ; subst. inversion H0 ; subst.
            left. inversion H1. reflexivity.
          }
          {
            simpl. intros. inversion H. inversion H0 ; subst.
            {
              apply reference_rule with (name := "LIGHT").
              { reflexivity. }
              { reflexivity. }
            }
            { inversion H0. }
          }
        }
        { simpl. apply lts_empty_rule. }
Qed.

(* Example 2.4 - Schneider, p. 32 (50) *)
Definition TICKET := "TICKET" ::= "cash" --> "ticket" --> "TICKET".
Definition CHANGE := "CHANGE" ::= "cash" --> "change" --> "CHANGE".
Definition MACHINE :=
  "MACHINE" ::= "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE".
Definition PARKING_PERMIT_MCH := Spec [Channel {{"cash", "ticket", "change"}}] [TICKET ; CHANGE ; MACHINE].

Example lts5 :
  ltsR
    PARKING_PERMIT_MCH
    [
      (* Tau transitions (process unfolding) *)
      ("TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE",
      Tau,
      "cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE") ;

          ("cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE",
          Tau,
          "cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE") ;

      ("TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE",
      Tau,
      "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE") ;

          ("TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE",
          Tau,
          "cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE") ;

      (* Synchronised event *)
      ("cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE",
      Event "cash",
      "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE") ;

      (* Advancing left side of the expression first... *)
      ("ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE",
      Event "ticket",
      "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE") ;

          (* ...then the right side. *)
          ("TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE",
          Event "change",
          "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE") ;

          (* Process unfolding (left side) *)
          ("TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE",
          Tau,
          "cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE") ;

              ("cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE",
              Event "change",
              "cash" --> "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE") ;

      (* Advancing right side of the expression first *)
      ("ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "change" --> "CHANGE",
      Event "change",
      "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE") ;

          (* ...then the left side. *)
          ("ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE",
          Event "ticket",
          "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE") ;

          (* Process unfolding (right side) *)
          ("ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "CHANGE",
          Tau,
          "ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE") ;

              ("ticket" --> "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE",
              Event "ticket",
              "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] "cash" --> "change" --> "CHANGE")
    ]
    "MACHINE".
Proof.
  unfold ltsR. split.
  (* TODO Find a way to automate this proof using Ltac. *)
  - repeat (apply NoDup_cons ; unfold not ; intros).
    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6. inversion H7.
    inversion H7. inversion H8.
    inversion H8. inversion H9.
    inversion H9. inversion H10.
    inversion H10. inversion H11.
    inversion H11.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6. inversion H7.
    inversion H7. inversion H8.
    inversion H8. inversion H9.
    inversion H9. inversion H10.
    inversion H10.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6. inversion H7.
    inversion H7. inversion H8.
    inversion H8. inversion H9.
    inversion H9. 

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6. inversion H7.
    inversion H7. inversion H8.
    inversion H8.
    
    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6. inversion H7.
    inversion H7.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4. inversion H5.
    inversion H5.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3. inversion H4.
    inversion H4.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2. inversion H3.
    inversion H3.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1. inversion H2.
    inversion H2.

    inversion H. inversion H0.
    inversion H0. inversion H1.
    inversion H1.

    inversion H. inversion H0.
    inversion H0.

    inversion H.

    apply NoDup_nil.
  - apply lts_inductive_rule.
    * intros. split.
      + intros. simpl in H. inversion H ; subst.
        { inversion H0. }
        { inversion H7 ; subst. inversion H8.
          { inversion H0. }
        }
        { inversion H7 ; subst. inversion H8.
          { inversion H0. }
        }
        { inversion H7 ; subst. inversion H0 ; subst. simpl in H. simpl in H7.
          { simpl. right. left. inversion H1. reflexivity. }
        }
        { inversion H7 ; subst. inversion H0 ; subst. simpl in H. simpl in H7.
          { simpl. left. inversion H1. reflexivity. }
        }
        { inversion H7 ; subst. inversion H9. inversion H0. }
        { inversion H8. }
      + simpl. intros.
        { inversion H.
          { inversion H0. apply alpha_parall_tau_indep_right_rule.
            apply reference_rule with (name := "CHANGE").
            { reflexivity. }
            { reflexivity. }
          }
          { inversion H0. inversion H1.
            { apply alpha_parall_tau_indep_left_rule.
              apply reference_rule with (name := "TICKET").
              { reflexivity. }
              { reflexivity. }
            }
            { contradiction. }
          }
        }
    * simpl. apply lts_inductive_rule.
      + split.
        { intros. inversion H ; subst. inversion H0. inversion H7 ; subst.
          inversion H8. inversion H0. inversion H7 ; subst. inversion H8.
          inversion H0. inversion H7 ; subst. inversion H0.
          inversion H7 ; subst. inversion H0 ; subst.
          { simpl. left. inversion H1. reflexivity. }
          inversion H7 ; subst. inversion H9. inversion H0.
          inversion H8.
        }
        { simpl. intros. inversion H. inversion H0 ; subst.
          { apply alpha_parall_tau_indep_right_rule.
            apply reference_rule with (name := "CHANGE").
            { reflexivity. }
            { reflexivity. }
          }
          inversion H0.
        }
      + simpl. apply lts_inductive_rule.
        { split.
          { intros. inversion H ; subst. inversion H0. inversion H7 ; subst.
            inversion H8. inversion H0. inversion H7 ; subst. inversion H8.
            inversion H0. inversion H7 ; subst. inversion H0.
            inversion H7 ; subst. inversion H0 ; subst. inversion H7 ; subst.
            inversion H9 ; subst. inversion H8 ; subst.
            { simpl. left. reflexivity. }
            inversion H0. inversion H7.
          }
          { simpl. intros. inversion H. inversion H0.
            { apply alpha_parall_joint_rule.
              { simpl. left. reflexivity. }
              { apply prefix_rule. }
              { apply prefix_rule. }
            }
            { inversion H0. }
          }
        }
        {
          simpl. apply lts_inductive_rule.
          { split.
            { intros. inversion H ; subst. inversion H0.
              inversion H7 ; subst. inversion H8 ; subst.
              { simpl. left. reflexivity. }
              inversion H0. inversion H7 ; subst. inversion H8 ; subst.
              { simpl. right. left. reflexivity. }
              inversion H0. inversion H7 ; subst. inversion H0.
              inversion H7 ; subst. inversion H0. inversion H7 ; subst.
              inversion H9. inversion H0. inversion H7 ; subst.
            }
            simpl. intros.
            { inversion H.
              { inversion H0. apply alpha_parall_indep_left_rule.
                { simpl. left. reflexivity. }
                { apply prefix_rule. }
              }
              { inversion H0.
                { inversion H1. apply alpha_parall_indep_right_rule.
                  { simpl. left. reflexivity. }
                  { apply prefix_rule. }
                }
                { inversion H1. }
              }
            }
          }
          { simpl. apply lts_inductive_rule.
            { split.
              { intros. simpl. inversion H ; subst.
                { inversion H0. }
                { inversion H7 ; subst.
                  { inversion H8 ; subst. right. left. reflexivity. }
                  { inversion H0. }
                }
                { inversion H7 ; subst.
                  { inversion H8 ; subst. }
                  { inversion H0. }
                }
                { inversion H7 ; subst. inversion H0. }
                { inversion H7 ; subst. inversion H0 ; subst.
                  { left. inversion H1. reflexivity. }
                }
                { inversion H7 ; subst. inversion H9. inversion H0. }
                { inversion H7. }
              }
              {
                intros. inversion H. inversion H0 ; subst.
                { apply alpha_parall_tau_indep_right_rule.
                  apply reference_rule with (name := "CHANGE").
                  { reflexivity. }
                  { reflexivity. }
                }
                inversion H0. inversion H1 ; subst.
                { apply alpha_parall_indep_left_rule.
                  { simpl. left. reflexivity. }
                  { apply prefix_rule. }
                }
                { inversion H1. }
              }
            }
            { simpl. apply lts_inductive_rule.
              { intros. split.
                { intros. simpl. inversion H ; subst. inversion H0.
                  inversion H7 ; subst. inversion H8 ; subst.
                  { left. reflexivity. }
                  { inversion H0. }
                  { inversion H7 ; subst. inversion H8. inversion H0. }
                  { inversion H7 ; subst. inversion H0. }
                  { inversion H7 ; subst. inversion H0. }
                  { inversion H7 ; subst. inversion H8. inversion H0. }
                  { inversion H7. }
                }
                {
                  simpl. intros. inversion H. inversion H0 ; subst.
                  { apply alpha_parall_indep_left_rule.
                    { simpl. left. reflexivity. }
                    { apply prefix_rule. }
                  }
                  { contradiction. }
                }
              }
              {
                simpl. apply lts_inductive_rule.
                { intros. split.
                  { intros. simpl. inversion H ; subst. inversion H0.
                    inversion H7 ; subst. inversion H8 ; subst. inversion H0.
                    inversion H7 ; subst. inversion H8 ; subst.
                    { right. left. reflexivity. }
                    { inversion H0. }
                    { inversion H7 ; subst. inversion H0 ; subst. simpl. left. inversion H1. reflexivity. }
                    { inversion H7 ; subst. inversion H0. }
                    inversion H7 ; subst. inversion H9. inversion H7 ; subst.
                    inversion H0. inversion H0.
                    { inversion H7. }
                  }
                  {
                    simpl. intros. inversion H. inversion H0 ; subst.
                    { apply alpha_parall_tau_indep_left_rule.
                      apply reference_rule with (name := "TICKET").
                      { reflexivity. }
                      { reflexivity. }
                    }
                    inversion H0. inversion H1 ; subst.
                    { apply alpha_parall_indep_right_rule.
                      { simpl. left. reflexivity. }
                      { apply prefix_rule. }
                    }
                    { contradiction. }
                  }
                }
                { simpl. apply lts_inductive_rule.
                  { simpl. intros. split.
                    { intros. inversion H ; subst. inversion H0. inversion H7 ; subst.
                      inversion H8. inversion H0. inversion H7 ; subst. inversion H8 ; subst.
                      { left. reflexivity. }
                      inversion H0. inversion H7 ; subst. inversion H0. inversion H7 ; subst.
                      inversion H0. inversion H7 ; subst. inversion H9. inversion H0.
                      inversion H8.
                    }
                    { intros. inversion H. inversion H0 ; subst.
                      { apply alpha_parall_indep_right_rule.
                        { simpl. left. reflexivity. }
                        { apply prefix_rule. }
                      }
                      inversion H0.
                    }
                  }
                  { simpl. apply lts_inductive_rule.
                    { simpl. split.
                      { intros. inversion H ; subst. inversion H0. inversion H7 ; subst.
                        inversion H8. inversion H0. inversion H7 ; subst. inversion H8.
                        inversion H0. inversion H7 ; subst. inversion H0 ; subst.
                        { simpl. left. inversion H1. reflexivity. }
                        { inversion H7 ; subst. inversion H0. }
                        inversion H7 ; subst. inversion H8 ; subst. inversion H0.
                        inversion H7.
                      }
                      { intros. inversion H. inversion H0.
                        apply alpha_parall_tau_indep_left_rule. eapply reference_rule.
                        reflexivity. reflexivity. inversion H0.
                      }
                    }
                    simpl. apply lts_empty_rule.
                  }
                }
              }
            } 
          }
        }
Qed.

Local Close Scope string.