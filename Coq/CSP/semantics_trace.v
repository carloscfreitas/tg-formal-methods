Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.
Require Import semantics_sos.

Definition trace := list event.

Inductive traceR' : specification -> proc_body -> trace -> Prop :=
  | empty_trace_rule (S : specification) (P : proc_body) :
    traceR' S P nil
  | event_trace_rule (S : specification) (P P' : proc_body) (h : event) (tl : trace) :
    (S # P // Event h ==> P') ->
    traceR' S P' tl ->
    traceR' S P (h::tl)
  | tick_trace_rule (S : specification) (P P' : proc_body) (t : trace) :
    (S # P // Tick ==> P') ->
    traceR' S P' t ->
    traceR' S P t
  | tau_trace_rule (S : specification) (P P' : proc_body) (t : trace) :
    (S # P // Tau ==> P') ->
    traceR' S P' t ->
    traceR' S P t.
  
Definition traceR (S : specification) (proc_name : string) (t : trace) :=
  match (get_proc_body S proc_name) with
  | Some body => traceR' S body t
  | None => False
  end.

Ltac solve_trace' :=
  multimatch goal with
  (* Empty trace *)
  | |- traceR' _ _ nil => apply empty_trace_rule
  (* Non-empty trace *)
  | |- traceR' _ _ _ =>
    (eapply tau_trace_rule
    + eapply tick_trace_rule
    + eapply event_trace_rule); solve_trace'
  (* SOS Prefix rule *)
  | |- _ # _ --> _ // _ ==> _ => apply prefix_rule
  (* SOS Reference rule *)
  | |- _ # ProcRef _ // _ ==> _ => eapply reference_rule; solve_trace'
  (* SOS External choice rule *)
  | |- _ # _ [] _ // _ ==> _ =>
    (eapply ext_choice_tau_left_rule
    + eapply ext_choice_tau_right_rule
    + eapply ext_choice_left_rule
    + eapply ext_choice_right_rule); solve_trace'
  (* SOS Internal choice *)
  | |- _ # _ |~| _ // _ ==> _ =>
    (eapply int_choice_left_rule
    + eapply int_choice_right_rule); solve_trace'
  (* SOS Alphabetised parallel *)
  | |- _ # _ [[ _ \\ _ ]] _ // _ ==> _ =>
    (eapply alpha_parall_tau_indep_left_rule
    + eapply alpha_parall_tau_indep_right_rule
    + eapply alpha_parall_tick_joint_rule
    + eapply alpha_parall_joint_rule
    + eapply alpha_parall_indep_left_rule
    + eapply alpha_parall_indep_right_rule); solve_trace'
  (* SOS Generalised parallel *)
  | |- _ # _ [| _ |] _ // _ ==> _ =>
    (eapply gener_parall_tau_indep_left_rule
    + eapply gener_parall_tau_indep_right_rule
    + eapply gener_parall_tick_joint_rule
    + eapply gener_parall_joint_rule
    + eapply gener_parall_indep_left_rule
    + eapply gener_parall_indep_right_rule); solve_trace'
  (* SOS Interleaving *)
  | |- _ # _ ||| _ // _ ==> _ =>
    (eapply interleave_tick_rule
    + eapply interleave_left_rule
    + eapply interleave_right_rule); solve_trace'
  (* SOS Sequential composition *)
  | |- _ # _ ;; _ // _ ==> _ =>
    (eapply seq_comp_tick_rule
    + eapply seq_comp_rule); solve_trace'
  (* SOS Hiding *)
  | |- _ # _ \ _ // _ ==> _ =>
    (eapply hiding_tau_tick_rule
    + eapply hiding_not_hidden_rule
    + eapply hiding_rule); solve_trace'
  (* Successful termination *)
  | |- _ # SKIP // Tick ==> _ => apply success_termination_rule
  (* Miscellaneous *)
  (* Not equal *)
  | |- _ <> _ => unfold not; let H := fresh "H" in (intros H; inversion H)
  (* Equal *)
  | |- _ = _ => reflexivity
  (* In *)
  | |- set_In _ _ => simpl; solve_trace'
  (* Not in *)
  | |- ~ set_In _ _ => solve_not_in
  (* Disjunction *)
  | |- _ \/ _ => (left + right); solve_trace'
  end.

Ltac solve_trace := unfold traceR; simpl; solve_trace'.

Definition trace_refinement (S : specification) (Spec Imp : string) : Prop :=
  forall (t : trace), traceR S Imp t -> traceR S Spec t.

Notation "S '#' P '[T=' Q" := (trace_refinement S P Q) (at level 150, left associativity).

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

Fixpoint get_transitions (S : specification) (P : proc_body) : option (list (event_tau_tick * proc_body)) :=
  match P with
  | SKIP => Some [(Tick, STOP)]
  | STOP => Some nil
  | e --> Q => Some [(Event e, Q)]
  | ProcRef name =>
    match get_proc_body S name with
    | Some Q => Some [(Tau, Q)]
    | None => None
    end
  | P' [] P'' =>
    match get_transitions S P', get_transitions S P'' with
    | Some t', Some t'' => Some (
      map (fun e => if (is_equal (fst e) Tau) then ((fst e), (snd e) [] P'') else e) t'
      ++ map (fun e => if (is_equal (fst e) Tau) then ((fst e), P' [] (snd e)) else e) t'')
    | _, _ => None
    end
  | P' |~| P'' => Some [(Tau, P') ; (Tau, P'')]
  | P' [[ A' \\ B' ]] P'' =>
    match get_transitions S P', get_transitions S P'' with
    | Some t', Some t'' =>
      let A := set_map event_tau_tick_eq_dec (fun x => Event x) A' in
      let B := set_map event_tau_tick_eq_dec (fun x => Event x) B' in
      let C := map (fun x => fst x) t' in
      let D := map (fun x => fst x) t'' in
      let U :=
        (* (C ⋂ ((A - B) ⋃ {τ}))           // Set of events P' can communicate independently.
          ⋃ (D ⋂ ((B - A) ⋃ {τ}))          // Set of events P'' can communicate independently.
          ⋃ ((C ⋂ D) ⋂ ((A ⋂ B) ⋃ {✓}))   // Set of events P' and P'' can communicate synchronously. *)
        set_union event_tau_tick_eq_dec (set_inter event_tau_tick_eq_dec C (set_add event_tau_tick_eq_dec Tau (set_diff event_tau_tick_eq_dec A B)))
        (set_union event_tau_tick_eq_dec (set_inter event_tau_tick_eq_dec D (set_add event_tau_tick_eq_dec Tau (set_diff event_tau_tick_eq_dec B A)))
        (set_inter event_tau_tick_eq_dec C (set_inter event_tau_tick_eq_dec D (set_add event_tau_tick_eq_dec Tick (set_inter event_tau_tick_eq_dec A B))))) in
      Some (filter (fun x => set_mem event_tau_tick_eq_dec (fst x) U) (alpha_parall_trans P' P'' t' t'' A' B' (set_inter event_tau_tick_eq_dec A B)))
    | _, _ => None
    end
  | P' [| A' |] P'' =>
    match get_transitions S P', get_transitions S P'' with
    | Some t', Some t'' =>
      let A := set_map event_tau_tick_eq_dec (fun x => Event x) A' in
      let B := map (fun x => fst x) t' in
      let C := map (fun x => fst x) t'' in
      let U := (* (B - A) ⋃ (C - A) ⋃ (A ⋂ B ⋂ C) *)
        set_union event_tau_tick_eq_dec (set_diff event_tau_tick_eq_dec B A)
        (set_union event_tau_tick_eq_dec (set_diff event_tau_tick_eq_dec C A)
        ((set_inter event_tau_tick_eq_dec A) ((set_inter event_tau_tick_eq_dec B) C))) in
      Some (filter (fun x => set_mem event_tau_tick_eq_dec (fst x) U) (gen_parall_trans P' P'' t' t'' A' A))
    | _, _ => None
    end
  | P' ||| P'' =>
    match get_transitions S P', get_transitions S P'' with
    | Some t', Some t'' => Some (
      map (fun e => ((fst e), (snd e) ||| P'')) t'
      ++ map (fun e => ((fst e), P' ||| (snd e))) t'')
    | _, _ => None
    end
  | P' ;; P'' =>
    match P' with
    | SKIP => Some [(Tau, P'')]
    | _ =>
      match get_transitions S P' with
      | Some t' => Some (map (fun e => ((fst e), (snd e) ;; P'')) t')
      | None => None
      end
    end
  | P' \ A =>
    match get_transitions S P' with
    | Some t' =>
      let A' := set_map event_tau_tick_eq_dec (fun x => Event x) A in
      Some (
        map (fun e =>
          if set_mem event_tau_tick_eq_dec (fst e) A'
          then (Tau, (snd e) \ A)
          else ((fst e), (snd e) \ A)) t'
      )
    | None => None
    end
  end.

Theorem get_transitions_correctness :
  forall (S : specification) (P : proc_body) (l : list (event_tau_tick * proc_body)),
    get_transitions S P = Some l -> forall (e : event_tau_tick) (P' : proc_body),
      In (e,P') l -> S # P // e ==> P'.
Proof.
  intros. generalize dependent l. induction P. (* TODO: destruct? *)
  (* SKIP *)
  - intros. simpl in H. inversion H. rewrite <- H2 in H0.
    simpl in H0. destruct H0.
    + inversion H0. apply success_termination_rule.
    + inversion H0.
  (* STOP *)
  - intros. simpl in H. inversion H. rewrite <- H2 in H0.
    simpl in H0. inversion H0.
  (* ProcRef *)
  - intros. simpl in H. destruct (get_proc_body S name) eqn:H'.
    + inversion H. rewrite <- H2 in H0.
      simpl in H0. destruct H0.
      * inversion H0. eapply reference_rule.
        { reflexivity. }
        { rewrite <- H4. apply H'. }
      * inversion H0.
    + inversion H.
  (* Prefix *)
  - intros. simpl in H. inversion H. rewrite <- H2 in H0.
    simpl in H0. destruct H0.
    + inversion H0. apply prefix_rule.
    + destruct H0.
  (* External Choice *)
  - intros. destruct P1. (* TODO: destruct P1 and P2? *)
    + destruct P2 ; simpl.
      * simpl in H. inversion H. rewrite <- H2 in H0. simpl in H0. destruct H0.
        { 
          inversion H0. apply ext_choice_left_rule.
          { 
            unfold not. intros. inversion H1.
          }
          {
            apply success_termination_rule.
          }
        }
        {
          destruct H0.
          {
            inversion H0. apply ext_choice_left_rule.
            {
              unfold not. intros. inversion H1.
            }
            {
              apply success_termination_rule.
            }
          }
          inversion H0.
        }
      * simpl in H. inversion H. rewrite <- H2 in H0. simpl in H0. destruct H0.
        { 
          inversion H0. apply ext_choice_left_rule.
          { 
            unfold not. intros. inversion H1.
          }
          {
            apply success_termination_rule.
          }
        }
        { 
          inversion H0.
        }
      * simpl in H. inversion H. destruct (get_proc_body S name) eqn:H2'.
        {
          simpl in H2. inversion H2. rewrite <- H3 in H0. destruct H0.
          {
            inversion H0. apply ext_choice_left_rule.
            {
              unfold not. intros H6. inversion H6.
            }
            {
              apply success_termination_rule.
            }
          }
          {
            simpl in H0. destruct H0.
            {
              inversion H0. apply ext_choice_tau_right_rule.
              {
                eapply reference_rule.
                {
                  reflexivity.
                }
                {
                  apply H2'.
                }
              }
            }
            {
              inversion H0.
            }
          }
        }
        {
          inversion H.
        }
Admitted.

(* TODO: get_transitions_completeness *)


Local Open Scope bool_scope.

Fixpoint check_trace'
  (S : specification)
  (P : proc_body)
  (event_list : trace)
  (fuel : nat) : option bool :=
  match fuel, event_list with
  | _, nil => Some true
  | O, _ => None 
  | S fuel', e :: es =>
    match get_transitions S P with
    | None => None
    | Some t =>
      let available_moves := t in
      let valid_moves := filter (
        fun t => (is_equal (fst t) (Event e))
          || (is_equal (fst t) Tau)
          || (is_equal (fst t) Tick)
      ) available_moves in
      match valid_moves with
      | nil => Some false
      | _ =>
        let result := map (fun t =>
          if is_equal (fst t) (Event e)
          then check_trace' S (snd t) es fuel'
          else check_trace' S (snd t) (e :: es) fuel'
        ) valid_moves in
        if existsb (fun o =>
          match o with
          | Some true => true
          | _ => false
          end) result
        then Some true
        else if forallb (fun o =>
          match o with
          | Some false => true
          | _ => false
          end) result
        then Some false
        else None
      end
    end
  end.

Definition check_trace
  (S : specification)
  (proc_id : string)
  (event_list : trace)
  (fuel : nat) : option bool :=
  match fuel, get_proc_body S proc_id with
  | O, _ | _, None => None
  | S fuel', Some P => check_trace' S P event_list fuel'
  end.

From QuickChick Require Import QuickChick.

(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Definition gen_valid_trans
  (S : specification)
  (P : proc_body)
  : G (option (list (event_tau_tick * proc_body))) :=
  match get_transitions S P with
  | None => ret None
  | Some nil => ret nil
  | Some (t :: ts) => bind (elems_ t (t :: ts)) (fun a => ret (Some [a]))
    (*
      a <- (elems (t :: ts)) ;;
      ret (Some [a])
    *)
  end.

Fixpoint gen_valid_trace'
  (S : specification)
  (P : proc_body)
  (size : nat)
  : G (option semantics_trace.trace) :=
  match size with
  | O => ret nil
  | S size' =>
    freq_ (ret nil) [
      (1, ret nil) ;
      (size,
        (*
          t <- gen_valid_trans S P ;;
          match t with
          | nil => ret nil
          | (Event e, Q) :: _ =>
            ts <- (gen_valid_trace' S Q size') ;;
            ret (e :: ts)
          | (_, Q) :: _ =>
            ts <- (gen_valid_trace' S Q size') ;;
            ret ts
          end
        *)
        bind (gen_valid_trans S P) (
          fun t => (
            match t with
            | nil => ret nil
            | (Event e, Q) :: _ =>
              bind (gen_valid_trace' S Q size') (
                fun ts => ret (e :: ts)
              )
            | (_, Q) :: _ =>
              bind (gen_valid_trace' S Q size') (
                fun ts => ret ts
              )
            end
          )
        )
      )
    ]
  end.

Definition gen_valid_trace
  (S : specification)
  (proc_id : string)
  (size : nat)
  : G (option semantics_trace.trace) :=
  match get_proc_body S proc_id with
  | None => ret None
  | Some P => gen_valid_trace' S P size
  end. 

Fixpoint gen_valid_ext_trace
  (S : specification)
  (P : proc_body)
  (size : nat)
  : G (option (list (event_tau_tick * proc_body))) :=
  match size with
  | O => ret nil
  | S size' =>
    freq_ (ret nil) [
      (1, ret nil) ;
      (size,
        (*
          t <- gen_valid_trans S P ;;
          match t with
          | nil => ret nil
          | x :: _ =>
            ts <- (gen_valid_ext_trace S (snd x) size') ;;
            ret (x :: ts)
          end
        *)
        bind (gen_valid_trans S P) (
          fun t => (
            match t with
            | nil => ret nil
            | x :: _ => bind (gen_valid_ext_trace S (snd x) size') (
              fun ts => ret (x :: ts)
            )
            end
          )
        )
      )
    ]
  end.

Instance show_event_tau_tick : Show event_tau_tick :=
{| show e := event_tau_tick_to_str e |}.

Instance show_proc_body : Show proc_body :=
{| show p := proc_body_to_str p |}.

Definition traceP
  (S : specification)
  (proc_id : string)
  (fuel : nat)
  (t : option semantics_trace.trace) : bool :=
  match t with
  | None => false
  | Some t' =>
    match check_trace S proc_id t' fuel with
    | None => false
    | Some b => b
    end
  end.

Definition trace_refinement_checker
  (S : specification)
  (Imp Spec : string)
  (trace_max_size : nat)
  (fuel : nat) : Checker :=
    forAll (gen_valid_trace S Imp trace_max_size) (traceP S Spec fuel).

Theorem traceP_correctness:
  forall (S : specification) (proc_id : string) (fuel : nat) (t : semantics_trace.trace),
  traceP S proc_id fuel (Some t) = true -> traceR S proc_id t.
Proof.
  intros. unfold traceR. destruct (get_proc_body S proc_id) eqn:H1.
  - unfold traceP in H. unfold check_trace in H. rewrite -> H1 in H.
    destruct fuel.
    * inversion H.
    * destruct (check_trace' S p t fuel) eqn:H2.
      + rewrite H in H2. destruct t.
        { apply empty_trace_rule. }
        {
          destruct fuel.
          { inversion H2. }
          {
            unfold check_trace' in H2. destruct (get_transitions S p) eqn:H3.
            destruct (filter (fun t : event_tau_tick * proc_body =>
              is_equal (fst t) (Event e) || is_equal (fst t) Tau || is_equal (fst t) Tick) l) eqn:H4.
            { inversion H2. }
            {
              admit.
            }
            { inversion H2. }
          }
        }
      + inversion H.
  - unfold traceP in H. unfold check_trace in H. rewrite -> H1 in H.
    destruct fuel; inversion H.
Admitted.


(** TRACE EXAMPLES **)

Local Open Scope string.

Definition CH_PRINTER0 := Channel {{"accept", "print"}}.
Definition PRINTER0 := "PRINTER0" ::= "accept" --> "print" --> STOP.
Definition S_PRINTER0 : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [CH_PRINTER0] [PRINTER0]).
Defined.

QuickChick (trace_refinement_checker S_PRINTER0 "PRINTER0" "PRINTER0" 3 1000).

Sample (gen_valid_trans S_PRINTER0 ("accept" --> "print" --> STOP)).

Sample (gen_valid_trace S_PRINTER0 "PRINTER0" 3).

Compute (check_trace S_PRINTER0 "PRINTER0" ["accept" ; "print"] 1000).

Example PRINTER0_empty_trace_auto : traceR S_PRINTER0 "PRINTER0" nil.
Proof. solve_trace. Qed.

Example PRINTER0_trace1_auto : traceR S_PRINTER0 "PRINTER0" ["accept"].
Proof. solve_trace. Qed.

Example PRINTER0_trace2_auto : traceR S_PRINTER0 "PRINTER0" ["accept" ; "print"].
Proof. solve_trace. Qed.

Definition CH_CHOOSE := Channel {{"select", "keep", "return"}}.
Definition P_CHOOSE := "CHOOSE" ::= "select" --> ("keep" --> SKIP
                                                [] "return" --> ProcRef "CHOOSE").
Definition S_CHOOSE : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [CH_CHOOSE] [P_CHOOSE]).
Defined.

QuickChick (trace_refinement_checker S_CHOOSE "CHOOSE" "CHOOSE" 20 1000).

Compute (get_transitions S_CHOOSE (("keep" --> SKIP [] "return" --> ProcRef "CHOOSE"))).

Sample (gen_valid_trace S_CHOOSE "CHOOSE" 5).

Compute (check_trace S_CHOOSE "CHOOSE" ["select" ; "return" ; "select" ; "return" ; "select" ; "keep"] 1000).

Example CHOOSE_trace1_auto : traceR S_CHOOSE "CHOOSE" ["select" ; "keep"].
Proof. solve_trace. Qed.

Example CHOOSE_trace2_auto : traceR S_CHOOSE "CHOOSE" ["select" ; "return"].
Proof. solve_trace. Qed.

Example CHOOSE_trace_auto : traceR S_CHOOSE "CHOOSE" ["select" ; "return" ; "select" ; "return" ; "select" ; "keep"].
Proof. solve_trace. Qed.

Definition CH_TEAM := Channel {{"lift_piano", "lift_table"}}.
Definition PETE := "PETE" ::= "lift_piano" --> ProcRef "PETE"
                              |~| "lift_table" --> ProcRef "PETE".

Definition DAVE := "DAVE" ::= "lift_piano" --> ProcRef "DAVE"
                              |~| "lift_table" --> ProcRef "DAVE".

Definition TEAM := "TEAM" ::= ProcRef "PETE" [| {{"lift_piano", "lift_table"}} |] ProcRef "DAVE".

Definition S_TEAM : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [CH_TEAM] [PETE ; DAVE ; TEAM]).
Defined.

Sample (gen_valid_trace S_TEAM "PETE" 5).

QuickChick (trace_refinement_checker S_TEAM "PETE" "DAVE" 20 1000).

Example TEAM_trace1_auto : traceR S_TEAM "TEAM" ["lift_piano"].
Proof. solve_trace. Qed.

Example TEAM_trace2_auto : traceR S_TEAM "TEAM" ["lift_piano"; "lift_table"].
Proof. solve_trace. Qed.

Example TEAM_trace3_auto : traceR S_TEAM "PETE" ["lift_table" ; "lift_piano" ; "lift_piano" ; "lift_piano" ; "lift_table"].
Proof. solve_trace. Qed.

Definition LIGHT := "LIGHT" ::= "on" --> "off" --> ProcRef "LIGHT".
Definition S_LIGHT : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [Channel {{"on", "off"}}] [LIGHT]).
Defined.

Example LIGHT_trace1_auto : traceR S_LIGHT "LIGHT" ["on"; "off" ; "on"].
Proof. solve_trace. Qed.

Definition S_FORECOURT : specification.
Proof.
  solve_spec_ctx_rules (
    Build_Spec
    [
      Channel {{"lift_nozzle_1", "lift_nozzle_1", "replace_nozzle_1", "depress_trigger_1", "release_trigger_1"}}
      ; Channel ["lift_nozzle_2" ; "replace_nozzle_2" ; "depress_trigger_2" ; "release_trigger_2"]
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

Example FORECOURT_trace1_auto : traceR S_FORECOURT "FORECOURT"
    ["lift_nozzle_1" ; "lift_nozzle_2" ; "depress_trigger_1" ; "depress_trigger_2" ; "release_trigger_2"].
Proof. solve_trace. Qed.

Example FORECOURT_trace2_auto : traceR S_FORECOURT "FORECOURT"
  ["lift_nozzle_1" ; "lift_nozzle_2" ; "depress_trigger_1" ; "depress_trigger_2" ; "release_trigger_2"
  ; "release_trigger_1" ; "replace_nozzle_2" ; "replace_nozzle_1" ; "lift_nozzle_2"].
Proof. solve_trace. Qed.

Definition SPY := "SPY" ::= "listen" --> "relay" --> ProcRef "SPY".
Definition MASTER := "MASTER" ::= "relay" --> "log" --> ProcRef "MASTER".
Definition MASTER_SPY := "MASTER_SPY" ::= ProcRef "SPY" [| {{"relay"}} |] ProcRef "MASTER" \ {{"relay"}}.
Definition S_MASTER_SPY : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [Channel {{"listen", "relay", "log"}}] [SPY ; MASTER ; MASTER_SPY]).
Defined.

Example MASTER_SPY_trace1_auto : traceR S_MASTER_SPY "MASTER_SPY" ["listen" ; "log"].
Proof. solve_trace. Qed.

Example MASTER_SPY_trace2_auto : traceR S_MASTER_SPY "MASTER_SPY" ["listen" ; "listen" ; "log" ; "listen" ; "log"].
Proof. solve_trace. Qed.

Definition S_PURCHASE : specification.
Proof.
  solve_spec_ctx_rules (
    Build_Spec 
    [
      Channel {{"select", "keep", "return"}}
      ; Channel {{"cash", "cheque", "card"}}
      ; Channel {{"swipe", "sign"}}
      ; Channel {{"receipt", "reject"}}
    ]
    [
      "CHOOSE" ::= "select" --> ("keep" --> SKIP 
                                [] "return" --> ProcRef "CHOOSE")
      ; "PAY" ::= "cash" --> "receipt" --> SKIP
                  [] "cheque" --> "receipt" --> SKIP
                  [] "card" --> "swipe" --> ("sign" --> "receipt" --> SKIP
                                            [] "reject" --> ProcRef "PAY")
      ; "PURCHASE" ::= ProcRef "CHOOSE" ;; ProcRef "PAY"
    ]
  ).
Defined.

Example PURCHASE_trace_auto : traceR S_PURCHASE "PURCHASE" ["select" ; "return" ; "select" ; "keep"
  ; "card" ; "swipe" ; "reject" ; "cash" ; "receipt"].
Proof. solve_trace. Qed.

Definition TICKET := "TICKET" ::= "cash" --> "ticket" --> ProcRef "TICKET".
Definition CHANGE := "CHANGE" ::= "cash" --> "change" --> ProcRef "CHANGE".
Definition MACHINE :=
  "MACHINE" ::= ProcRef "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] ProcRef "CHANGE".
Definition PARKING_PERMIT_MCH : specification.
Proof.
  solve_spec_ctx_rules (Build_Spec [Channel {{"cash", "ticket", "change"}}] [TICKET ; CHANGE ; MACHINE]).
Defined.

Example PARKING_trace_auto : traceR PARKING_PERMIT_MCH "MACHINE" ["cash" ; "ticket" ; "change" ; "cash" ; "change" ; "ticket"].
Proof. solve_trace. Qed.

Definition TOY_PROBLEM : specification.
Proof.
  solve_spec_ctx_rules (
    Build_Spec
    [Channel {{"a", "b"}}]
    [
      ("P" ::= "a" --> STOP)
      ; ("Q" ::= "a" --> "b" --> STOP)
      ; ("R" ::= ProcRef "P" [] ProcRef "Q")
    ]
  ).
Defined.
Example TOY_PROBLEM_trace_auto : traceR TOY_PROBLEM "R" ["a" ; "b"].
Proof. solve_trace. Qed.

Local Close Scope string.