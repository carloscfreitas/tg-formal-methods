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

Definition is_equal (a : event_tau_tick) (b : event_tau_tick) : bool := eqb a b.

Fixpoint gen_parall_trans'
  (left_hand_proc : proc_body)
  (right_hand_proc_trans : list (event_tau_tick * proc_body))
  (alpha : set event)
  (sync_events : set event_tau_tick)
  : list (event_tau_tick * proc_body) :=
  match right_hand_proc_trans with
  | (e, P) :: l =>
    if set_mem event_tau_tick_eq_dec e sync_events
    then gen_parall_trans' left_hand_proc l alpha sync_events
    else (e, left_hand_proc [| alpha |] P)
      :: (gen_parall_trans' left_hand_proc l alpha sync_events)
  | nil => nil
  end.

Fixpoint gen_parall_trans
  (left_hand_proc : proc_body)
  (right_hand_proc : proc_body)
  (left_hand_proc_trans : list (event_tau_tick * proc_body))
  (right_hand_proc_trans : list (event_tau_tick * proc_body))
  (alpha : set event)
  (sync_events : set event_tau_tick)
  : list (event_tau_tick * proc_body) :=
  match left_hand_proc_trans with
  | (e, P) :: l =>
    if ((set_mem event_tau_tick_eq_dec e sync_events) || (is_equal e Tick))%bool
    then (map (fun x => (e, P [| alpha |] (snd x)))
      (filter (fun x => is_equal e (fst x)) right_hand_proc_trans))
      ++ (gen_parall_trans left_hand_proc right_hand_proc l right_hand_proc_trans alpha sync_events)
    else (e, P [| alpha |] right_hand_proc) 
      :: (gen_parall_trans left_hand_proc right_hand_proc l right_hand_proc_trans alpha sync_events)
  | nil => gen_parall_trans' left_hand_proc right_hand_proc_trans alpha sync_events
  end.

Fixpoint alpha_parall_trans'
  (left_hand_proc : proc_body)
  (right_hand_proc_trans : list (event_tau_tick * proc_body))
  (alpha1 : set event)
  (alpha2 : set event)
  (sync_events : set event_tau_tick)
  : list (event_tau_tick * proc_body) :=
  match right_hand_proc_trans with
  | (e, P) :: l =>
    if set_mem event_tau_tick_eq_dec e sync_events
    then alpha_parall_trans' left_hand_proc l alpha1 alpha2 sync_events
    else (e, left_hand_proc [[ alpha1 \\ alpha2 ]] P)
      :: (alpha_parall_trans' left_hand_proc l alpha1 alpha2 sync_events)
  | nil => nil
  end.

Fixpoint alpha_parall_trans
  (left_hand_proc : proc_body)
  (right_hand_proc : proc_body)
  (left_hand_proc_trans : list (event_tau_tick * proc_body))
  (right_hand_proc_trans : list (event_tau_tick * proc_body))
  (alpha1 : set event)
  (alpha2 : set event)
  (sync_events : set event_tau_tick)
  : list (event_tau_tick * proc_body) :=
  match left_hand_proc_trans with
  | (e, P) :: l =>
    if ((set_mem event_tau_tick_eq_dec e sync_events) || (is_equal e Tick))%bool
    then (map (fun x => (e, P [[ alpha1 \\ alpha2 ]] (snd x)))
      (filter (fun x => is_equal e (fst x)) right_hand_proc_trans))
      ++ (alpha_parall_trans left_hand_proc right_hand_proc l right_hand_proc_trans alpha1 alpha2 sync_events)
    else (e, P [[ alpha1 \\ alpha2 ]] right_hand_proc) 
      :: (alpha_parall_trans left_hand_proc right_hand_proc l right_hand_proc_trans alpha1 alpha2 sync_events)
  | nil => alpha_parall_trans' left_hand_proc right_hand_proc_trans alpha1 alpha2 sync_events
  end.

Fixpoint get_transitions (S : specification) (P : proc_body) : list (event_tau_tick * proc_body) :=
  match P with
  | SKIP => [(Tick, STOP)]
  | STOP => nil
  | e --> Q => [(Event e, Q)]
  | ProcRef name =>
    match get_proc_body S name with
    | Some Q => [(Tau, Q)]
    | None => nil
    end
  | P' [] P'' =>
    map (fun e => if (is_equal (fst e) Tau) then ((fst e), (snd e) [] P'') else e) (get_transitions S P')
    ++ map (fun e => if (is_equal (fst e) Tau) then ((fst e), P' [] (snd e)) else e) (get_transitions S P'')
  | P' |~| P'' => [(Tau, P') ; (Tau, P'')]
  | P' [[ A' \\ B' ]] P'' =>
    let A := set_map event_tau_tick_eq_dec (fun x => Event x) A' in
    let B := set_map event_tau_tick_eq_dec (fun x => Event x) B' in
    let t' := get_transitions S P' in
    let C := map (fun x => fst x) t' in
    let t'' := get_transitions S P'' in
    let D := map (fun x => fst x) t'' in
    let U :=
      (* (C ⋂ ((A - B) ⋃ {τ}))           // Set of events P' can communicate independently.
        ⋃ (D ⋂ ((B - A) ⋃ {τ}))          // Set of events P'' can communicate independently.
        ⋃ ((C ⋂ D) ⋂ ((A ⋂ B) ⋃ {✓}))   // Set of events P' and P'' can communicate synchronously. *)
      set_union event_tau_tick_eq_dec (set_inter event_tau_tick_eq_dec C (set_add event_tau_tick_eq_dec Tau (set_diff event_tau_tick_eq_dec A B)))
      (set_union event_tau_tick_eq_dec (set_inter event_tau_tick_eq_dec D (set_add event_tau_tick_eq_dec Tau (set_diff event_tau_tick_eq_dec B A)))
      (set_inter event_tau_tick_eq_dec C (set_inter event_tau_tick_eq_dec D (set_add event_tau_tick_eq_dec Tick (set_inter event_tau_tick_eq_dec A B))))) in
    filter (fun x => set_mem event_tau_tick_eq_dec (fst x) U) (alpha_parall_trans P' P'' t' t'' A' B' (set_inter event_tau_tick_eq_dec A B))
  | P' [| A' |] P'' =>
    let A := set_map event_tau_tick_eq_dec (fun x => Event x) A' in
    let t' := get_transitions S P' in
    let B := map (fun x => fst x) t' in
    let t'' := get_transitions S P'' in
    let C := map (fun x => fst x) t'' in
    let U := (* (B - A) ⋃ (C - A) ⋃ (A ⋂ B ⋂ C) *)
      set_union event_tau_tick_eq_dec (set_diff event_tau_tick_eq_dec B A)
      (set_union event_tau_tick_eq_dec (set_diff event_tau_tick_eq_dec C A)
      ((set_inter event_tau_tick_eq_dec A) ((set_inter event_tau_tick_eq_dec B) C))) in
    filter (fun x => set_mem event_tau_tick_eq_dec (fst x) U) (gen_parall_trans P' P'' t' t'' A' A)
    | P' ||| P'' =>
    map (fun e => ((fst e), (snd e) ||| P'')) (get_transitions S P')
    ++ map (fun e => ((fst e), P' ||| (snd e))) (get_transitions S P'')
  | P' ;; P'' =>
    match P' with
    | SKIP => [(Tau, P'')]
    | _ => map (fun e => ((fst e), (snd e) ;; P'')) (get_transitions S P')
    end
  | P' \ A => let A' := set_map event_tau_tick_eq_dec (fun x => Event x) A in
    map (fun e =>
      if set_mem event_tau_tick_eq_dec (fst e) A'
      then (Tau, (snd e) \ A)
      else ((fst e), (snd e) \ A)) (get_transitions S P')
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

Local Open Scope string.

Definition S_FORECOURT :=
(
  Spec
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
Compute generate_dot (compute_ltsR S_FORECOURT "FORECOURT" 100).

Definition TOY' := Spec [Channel {{"a", "b"}}] ["P" ::= "b" --> SKIP [] "a" --> STOP \ {{"a"}}].
Compute generate_dot( compute_ltsR TOY' "P" 10).

Definition CH := Channel {{"a", "b"}}.
Definition P := "P" ::= "a" --> STOP [] "b" --> "b" --> STOP.
Definition S := Spec [CH] [P].

Compute generate_dot (compute_ltsR S "P" 100).

Definition CH_TEAM := Channel {{"lift_piano", "lift_table"}}.
Definition PETE := "PETE" ::= "lift_piano" --> ProcRef "PETE"
                              |~| "lift_table" --> ProcRef "PETE".

Definition DAVE := "DAVE" ::= "lift_piano" --> ProcRef "DAVE"
                              |~| "lift_table" --> ProcRef "DAVE".

Definition TEAM := "TEAM" ::= ProcRef "PETE" [| {{"lift_piano", "lift_table"}} |] ProcRef "DAVE".

Definition S_TEAM := Spec [CH_TEAM] [PETE ; DAVE ; TEAM].

Compute generate_dot (compute_ltsR S_TEAM "TEAM" 100).

Definition TOY_PROBLEM := Spec [Channel {{"a", "b"}}] ["P" ::= "a" --> "b" --> STOP].

Compute generate_dot (compute_ltsR TOY_PROBLEM "P" 100).

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

Compute generate_dot (compute_ltsR TOY_PROBLEM' "P" 100).

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
Definition UNDERDEFINED_RECURSION := Spec [Channel {{}}] [P'].

Compute generate_dot (compute_ltsR UNDERDEFINED_RECURSION "P" 100).

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

Definition S_LIGHT := Spec [Channel {{"on", "off"}}] ["LIGHT" ::= "on" --> "off" --> ProcRef "LIGHT"].

Compute generate_dot (compute_ltsR S_LIGHT "LIGHT" 100).

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
Definition PARKING_PERMIT_MCH := Spec [Channel {{"cash", "ticket", "change"}}] [TICKET ; CHANGE ; MACHINE].

Compute generate_dot (compute_ltsR PARKING_PERMIT_MCH "MACHINE" 100).

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