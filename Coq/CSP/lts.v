Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.
Require Import semantics_sos.
Require Import semantics_trace.

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
  | lts_empty_rule (S : specification) (visited : set proc_body) :
      ltsR' S nil nil visited
  | lts_inductive_rule
        (S : specification)
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
         (S # P // a ==> P') <-> In (P,a,P') T') ->
      ltsR' S T'' to_visit visited' ->
      ltsR' S T (P :: tl) visited.

Definition ltsR (S : specification) (T : set transition) (name : string) : Prop :=
  match get_proc_body S name with
  | Some body => NoDup T /\ ltsR' S T [body] nil
  | None => False
  end.

Fixpoint compute_ltsR'
  (S : specification)
  (states_to_visit : set proc_body)
  (visited_states : set proc_body)
  (limit : nat)
  : option (set transition) :=
  match limit, states_to_visit with
  | _, nil => Some (empty_set transition)
  | 0, state :: tl => None
  | S n, state :: tl =>
    let action_state_list := get_transitions S state in
    let state_transitions := map (fun e => (state, (fst e), (snd e))) action_state_list in
    match
      compute_ltsR'
        S
        (set_union proc_body_eq_dec (set_diff proc_body_eq_dec (target_proc_bodies state_transitions) visited_states) tl)
        (set_add proc_body_eq_dec state visited_states)
        n with
    | Some all_transitions => Some (set_union transition_eq_dec state_transitions all_transitions)
    | None => None
    end
  end.

Definition compute_ltsR (S : specification) (name : string) (limit : nat) : option (set transition) :=
  match get_proc_body S name with
  | Some body => compute_ltsR' S [body] nil limit
  | None => None
  end.

Fixpoint generate_dot' (lts : set transition) : string :=
  match lts with
  | nil => ""
  | (P, e, Q) :: tl => " <" ++ P ++ "> -> <" ++ Q ++ ">" ++ " [label=<" ++ e ++ ">];" ++ (generate_dot' tl)
  end.

Definition style_initial_state (P : proc_body) : string := "<" ++ P ++ "> [style=bold, color=red];".

Definition generate_dot (lts : option (set transition)) : string :=
  match lts with
  | Some ((P, e, Q) :: tl) =>
    "digraph LTS { " ++ (style_initial_state P) ++ (generate_dot' ((P, e, Q) :: tl)) ++ " }"
  | _ => ""
  end.

Theorem compute_ltsR_step_more:
  forall (S : specification) (l l' : set proc_body) (n : nat) (trans_set : set transition),
  compute_ltsR' S l l' n = Some trans_set ->
  compute_ltsR' S l l' (n + 1) = Some trans_set.
Proof. Admitted.

Theorem compute_ltsR_correctness:
  forall (S : specification) (proc_id : string) (n : nat) (trans_set : set transition),
  compute_ltsR S proc_id n = Some trans_set -> ltsR S trans_set proc_id.
Proof.
  intros. destruct (get_proc_body S proc_id) eqn:H1.
  - destruct p.
    * (* SKIP *)
      unfold compute_ltsR in H; rewrite -> H1 in H. destruct n.
      + inversion H.
      + simpl in H. destruct n.
        { inversion H. }
        {
          inversion H. destruct n.
          {
            inversion H2. unfold ltsR. rewrite -> H1. split.
            { solve_nodup. }
            { 
              apply lts_inductive_rule.
              {
                split.
                {
                  intros. inversion H0; subst.
                  { inversion H4. }
                  { simpl. left. reflexivity. }
                }
                {
                  intros.
                  {
                    inversion H0.
                    { inversion H4; subst. apply success_termination_rule. }
                    { inversion H4. }
                  }
                }
              }
              simpl. apply lts_inductive_rule.
              {
                split.
                { intros. inversion H0; subst. inversion H4. }
                { simpl. intros. contradiction. }
              }
              simpl. apply lts_empty_rule.
            }
          } 
          {
            inversion H2. unfold ltsR. rewrite -> H1. split.
            { solve_nodup. }
            { 
              apply lts_inductive_rule.
              {
                split.
                {
                  intros. inversion H0; subst.
                  { inversion H4. }
                  { simpl. left. reflexivity. }
                }
                {
                  intros.
                  {
                    inversion H0.
                    { inversion H4; subst. apply success_termination_rule. }
                    { inversion H4. }
                  }
                }
              }
              simpl. apply lts_inductive_rule.
              {
                split.
                { intros. inversion H0; subst. inversion H4. }
                { simpl. intros. contradiction. }
              }
              simpl. apply lts_empty_rule.
            }
          }
        }
    * (* STOP *)
      unfold compute_ltsR in H; rewrite -> H1 in H. destruct n.
      + inversion H.
      + inversion H. destruct n.
        { 
          inversion H2. unfold ltsR. rewrite -> H1.
          split.
          { apply NoDup_nil. }
          {
            apply lts_inductive_rule.
            {
              split.
              { intros. inversion H0; subst. inversion H4. }
              { simpl. intros. contradiction. }
            }
            simpl. apply lts_empty_rule. 
          }
        }
        { 
          inversion H2. unfold ltsR. rewrite -> H1.
          split.
          { apply NoDup_nil. }
          {
            apply lts_inductive_rule.
            {
              split.
              { intros. inversion H0; subst. inversion H4. }
              { simpl. intros. contradiction. }
            }
            simpl. apply lts_empty_rule. 
          }
        }
    * (* ProcRef name *)
      unfold ltsR. rewrite -> H1. split.
      + unfold compute_ltsR in H. rewrite -> H1 in H.
        induction n.
        { inversion H. }
        {
          inversion H. destruct (get_proc_body S name) eqn:H3.
          {
            inversion H2. destruct (compute_ltsR' S [p] [ProcRef name] n) eqn:H5.
            {
              inversion H4. induction s.
              { simpl. solve_nodup. }
              { unfold set_union. unfold set_add. admit. }
            }
            { inversion H4. }
          }
          { inversion H2. admit. }
        }
      + apply lts_inductive_rule.
        {
          split.
          {
            intros. inversion H0; subst. unfold compute_ltsR in H; rewrite -> H1 in H.
            destruct n.
            { inversion H. }
            { 
              inversion H. destruct (get_proc_body S name).
              { inversion H5. admit. }
              admit.
            }
          }
          admit.
        }
        admit.
    * (* e --> P *)
      unfold compute_ltsR in H; rewrite -> H1 in H. induction n.
      + inversion H.
      + inversion H. destruct (compute_ltsR' S [p] [event --> p] n) eqn:H3.
        {
          induction s.
          {
            inversion H2. unfold ltsR. rewrite H1. split.
            { solve_nodup. }
            {
              apply lts_inductive_rule.
              {
                split.
                {
                  intros. inversion H0; subst.
                  {
                    unfold transitions_from_P. destruct proc_body_eq_dec.
                    { simpl. left. reflexivity. }
                    { contradiction. }
                  }
                  { inversion H5. }
                }
                {
                  unfold transitions_from_P. destruct proc_body_eq_dec.
                  {
                    intros. inversion H0.
                    { inversion H5. apply prefix_rule. }
                    { inversion H5. }
                  }
                  { contradiction. }
                }
              }
              {
                unfold transitions_from_P. destruct proc_body_eq_dec.
                { 
                  unfold set_add. unfold target_proc_bodies. 
                  unfold set_add. unfold set_union. unfold set_add.
                  unfold set_diff. unfold set_mem. destruct transition_eq_dec.
                  {
                    destruct proc_body_eq_dec.
                    { apply lts_empty_rule. }
                    {
                      simpl. apply lts_inductive_rule.
                      {
                        split.
                        { 
                          intros. simpl. inversion H0; subst; admit.
                        }
                        { admit. }
                      }
                      admit.
                    }
                  }
                  { contradiction. }
                }
                { contradiction. }
              }
            }
          }
          admit.
        }
        { inversion H2. }
Admitted.

Local Open Scope string.

Definition S_FORECOURT :  specification.
Proof.
  solve_spec_ctx_rules (
    Build_Spec
    [
      Channel {{"lift_nozzle_1", "replace_nozzle_1", "depress_trigger_1", "release_trigger_1"}}
      ; Channel {{"lift_nozzle_2", "replace_nozzle_2", "depress_trigger_2", "release_trigger_2"}}
    ]
    [
      "PUMP1" ::= "lift_nozzle_1" --> ProcRef "READY1"
      ; "READY1" ::= "replace_nozzle_1" --> ProcRef "PUMP1"
                      [] "depress_trigger_1" --> "release_trigger_1" --> ProcRef "READY1"
      ; "PUMP2" ::= "lift_nozzle_2" --> ProcRef "READY2"
      ; "READY2" ::= "replace_nozzle_2" --> ProcRef "PUMP2"
                      [] "depress_trigger_2" --> "release_trigger_2" --> ProcRef "READY2"
      ; "FORECOURT" ::= ProcRef "PUMP1" ||| ProcRef "PUMP2"
    ]
  ).
Defined.

Definition TOY' : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [Channel {{"a", "b"}}] ["P" ::= "b" --> SKIP [] "a" --> STOP \ {{"a"}}]).
Defined.

Definition CH := Channel {{"a", "b"}}.
Definition P := "P" ::= "a" --> STOP [] "b" --> "b" --> STOP.
Definition S : specification.
Proof. solve_spec_ctx_rules (Build_Spec [CH] [P]). Defined.

Definition CH_TEAM := Channel {{"lift_piano", "lift_table"}}.
Definition PETE := "PETE" ::= "lift_piano" --> ProcRef "PETE"
                              |~| "lift_table" --> ProcRef "PETE".

Definition DAVE := "DAVE" ::= "lift_piano" --> ProcRef "DAVE"
                              |~| "lift_table" --> ProcRef "DAVE".

Definition TEAM := "TEAM" ::= ProcRef "PETE" [| {{"lift_piano", "lift_table"}} |] ProcRef "DAVE".

Definition S_TEAM : specification.
Proof. solve_spec_ctx_rules (Build_Spec [CH_TEAM] [PETE ; DAVE ; TEAM]). Defined.

Definition TOY_PROBLEM : specification.
Proof. solve_spec_ctx_rules (Build_Spec [Channel {{"a", "b"}}] ["P" ::= "a" --> "b" --> STOP]). Defined.

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

Definition TOY_PROBLEM' : specification.
Proof.
  solve_spec_ctx_rules (
    Build_Spec
    [Channel {{"a", "b", "c"}}]
    ["P" ::= ("a" --> "b" --> STOP) [] ("c" --> STOP)]
  ).
Defined.

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

Definition P' := "P" ::= ProcRef "P".
Definition UNDERDEFINED_RECURSION : specification.
Proof. solve_spec_ctx_rules (Build_Spec [Channel {{}}] [P']). Defined.

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

Definition S_LIGHT : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [Channel {{"on", "off"}}] ["LIGHT" ::= "on" --> "off" --> ProcRef "LIGHT"]).
Defined.

Example lts4 :
  ltsR
    S_LIGHT
    [
      ("on" --> "off" --> ProcRef "LIGHT", Event "on", "off" --> ProcRef "LIGHT") ; 
      ("off" --> ProcRef "LIGHT", Event "off", ProcRef "LIGHT") ;
      (ProcRef "LIGHT", Tau, "on" --> "off" --> ProcRef "LIGHT")
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
Definition TICKET := "TICKET" ::= "cash" --> "ticket" --> ProcRef "TICKET".
Definition CHANGE := "CHANGE" ::= "cash" --> "change" --> ProcRef "CHANGE".
Definition MACHINE := "MACHINE" ::= ProcRef "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] ProcRef "CHANGE".
Definition PARKING_PERMIT_MCH : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [Channel {{"cash", "ticket", "change"}}] [TICKET ; CHANGE ; MACHINE]).
Defined.

(*
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
*)
Local Close Scope string.