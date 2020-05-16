Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.
Require Import semantics_sos.

Definition trace := list event.
Definition extendedTrace := list event_tau_tick.

Inductive traceR' : specification -> proc_body -> trace -> Prop :=
  | empty_trace_rule (C : specification) (P : proc_body) :
    traceR' C P nil
  | event_trace_rule (C : specification) (P P' : proc_body) (h : event) (tl : trace) :
    (C # P // Event h ==> P') ->
    traceR' C P' tl ->
    traceR' C P (h::tl)
  | tick_trace_rule (C : specification) (P P' : proc_body) (t : trace) :
    (C # P // Tick ==> P') ->
    traceR' C P' t ->
    traceR' C P t
  | tau_trace_rule (C : specification) (P P' : proc_body) (t : trace) :
    (C # P // Tau ==> P') ->
    traceR' C P' t ->
    traceR' C P t.
  
Definition traceR (C : specification) (proc_name : string) (t : trace) :=
  match (get_proc_body C proc_name) with
  | Some body => traceR' C body t
  | None => False
  end.

Fixpoint get_trace (t : extendedTrace) : trace :=
  match t with
  | nil     => nil
  | h :: tl => match h with
               | Event e  => e :: get_trace tl
               | _        => get_trace tl
               end
  end.

Definition extendedTraceR' (C : specification) (body : proc_body) (t : extendedTrace) :=
  exists (body' : proc_body), C # body /// t ==> body'.
  
Definition extendedTraceR (C : specification) (proc_name : string) (t : extendedTrace) :=
  match (get_proc_body C proc_name) with
  | Some body => extendedTraceR' C body t
  | None => False
  end.

Ltac solve_not_in := unfold not; let H := fresh "H" in (intros H; repeat (contradiction + (destruct H; [> inversion H | ]))).

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

(** TRACE EXAMPLES **)

Local Open Scope string.

Definition CH_PRINTER0 := Channel {{"accept", "print"}}.
Definition PRINTER0 := "PRINTER0" ::= "accept" --> "print" --> STOP.
Definition S_PRINTER0 := Spec [CH_PRINTER0] [PRINTER0].

Example PRINTER0_empty_trace : traceR S_PRINTER0 "PRINTER0" nil.
Proof.
  unfold traceR. simpl.
  apply empty_trace_rule.
Qed.

Example PRINTER0_empty_trace_auto : traceR S_PRINTER0 "PRINTER0" nil.
Proof. solve_trace. Qed.

Example PRINTER0_empty_trace' : extendedTraceR S_PRINTER0 "PRINTER0" nil.
Proof.
  unfold extendedTraceR. simpl. unfold extendedTraceR'.
  eexists. apply sos_empty_rule.
Qed.

Example PRINTER0_trace1 : traceR S_PRINTER0 "PRINTER0" ["accept"].
Proof.
  unfold traceR. simpl.
  eapply event_trace_rule.
  - apply prefix_rule.
  - apply empty_trace_rule.
Qed.

Example PRINTER0_trace1_auto : traceR S_PRINTER0 "PRINTER0" ["accept"].
Proof. solve_trace. Qed.

Example PRINTER0_trace1' : extendedTraceR S_PRINTER0 "PRINTER0" [Event "accept"].
Proof.
  unfold extendedTraceR. simpl. unfold extendedTraceR'.
  eexists. eapply sos_transitive_rule.
    - apply prefix_rule.
    - apply sos_empty_rule. 
Qed.

Example PRINTER0_trace2 : traceR S_PRINTER0 "PRINTER0" ["accept" ; "print"].
Proof.
  unfold traceR. simpl.
  eapply event_trace_rule.
  - apply prefix_rule.
  - eapply event_trace_rule.
    + apply prefix_rule.
    + apply empty_trace_rule.
Qed.

Example PRINTER0_trace2_auto : traceR S_PRINTER0 "PRINTER0" ["accept" ; "print"].
Proof. solve_trace. Qed.

Example PRINTER0_trace2' : extendedTraceR S_PRINTER0 "PRINTER0" [Event "accept" ; Event "print"].
Proof.
  unfold extendedTraceR. simpl.
  eexists. apply sos_transitive_rule with (R := "print" --> STOP).
    - apply prefix_rule.
    - apply sos_transitive_rule with (R := STOP).
      + apply prefix_rule.
      + apply sos_empty_rule.
Qed.
*)
Definition CH_CHOOSE := Channel {{"select", "keep", "return"}}.
Definition P_CHOOSE := "CHOOSE" ::= "select" --> ("keep" --> SKIP
                                                [] "return" --> ProcRef "CHOOSE").
Definition S_CHOOSE := Spec [CH_CHOOSE] [P_CHOOSE].

Example CHOOSE_trace1 : traceR S_CHOOSE "CHOOSE" ["select" ; "keep"].
Proof.
  unfold traceR. simpl.
  eapply event_trace_rule.
  - apply prefix_rule.
  - eapply event_trace_rule.
    * apply ext_choice_left_rule.
      + unfold not. intros. inversion H.
      + apply prefix_rule.
    * apply empty_trace_rule.
Qed.

Example CHOOSE_trace1_auto : traceR S_CHOOSE "CHOOSE" ["select" ; "keep"].
Proof. solve_trace. Qed.

Example CHOOSE_trace1' : extendedTraceR S_CHOOSE "CHOOSE" [Event "select" ; Event "keep"].
Proof.
  unfold extendedTraceR. simpl. eexists.
  apply sos_transitive_rule with (R := "keep" --> SKIP [] "return" --> ProcRef "CHOOSE").
    - apply prefix_rule.
    - apply sos_transitive_rule with (R := SKIP).
      * apply ext_choice_left_rule.
        + unfold not. intros. inversion H.
        + apply prefix_rule.
      * apply sos_empty_rule.
Qed.

Example CHOOSE_trace2 : traceR S_CHOOSE "CHOOSE" ["select" ; "return"].
Proof.
  unfold traceR. simpl.
  eapply event_trace_rule.
  - apply prefix_rule.
  - eapply event_trace_rule.
    * apply ext_choice_right_rule.
      + unfold not. intros. inversion H.
      + apply prefix_rule.
    * apply empty_trace_rule.
Qed.

Example CHOOSE_trace2_auto : traceR S_CHOOSE "CHOOSE" ["select" ; "return"].
Proof. solve_trace. Qed.

Example CHOOSE_trace2' : extendedTraceR S_CHOOSE "CHOOSE" [Event "select" ; Event "return"].
Proof.
  unfold extendedTraceR. simpl.
  eexists. eapply sos_transitive_rule.
    - apply prefix_rule.
    - eapply sos_transitive_rule.
      * apply ext_choice_right_rule.
        + unfold not. intros. inversion H.
        + apply prefix_rule.
      * apply sos_empty_rule.
Qed.

Example CHOOSE_trace_auto : traceR S_CHOOSE "CHOOSE" ["select" ; "return" ; "select" ; "return" ; "select" ; "keep"].
Proof. solve_trace. Qed.

Definition CH_TEAM := Channel {{"lift_piano", "lift_table"}}.
Definition PETE := "PETE" ::= "lift_piano" --> ProcRef "PETE"
                              |~| "lift_table" --> ProcRef "PETE".

Definition DAVE := "DAVE" ::= "lift_piano" --> ProcRef "DAVE"
                              |~| "lift_table" --> ProcRef "DAVE".

Definition TEAM := "TEAM" ::= ProcRef "PETE" [| {{"lift_piano", "lift_table"}} |] ProcRef "DAVE".

Definition S_TEAM := Spec [CH_TEAM] [PETE ; DAVE ; TEAM].
(*
Example TEAM_trace1 : traceR S_TEAM "TEAM" ["lift_piano"].
Proof.
  unfold traceR. simpl.
  eapply tau_trace_rule.
  - apply gener_parall_tau_indep_left_rule. eapply reference_rule.
    + reflexivity.
    + reflexivity.
  - eapply tau_trace_rule.
    + apply gener_parall_tau_indep_right_rule. eapply reference_rule.
      * reflexivity.
      * reflexivity.
    + simpl. eapply tau_trace_rule.
      * apply gener_parall_tau_indep_left_rule. apply int_choice_left_rule.
      * eapply tau_trace_rule.
        { apply gener_parall_tau_indep_right_rule. apply int_choice_left_rule. }
        {
          eapply event_trace_rule.
          {
            apply gener_parall_joint_rule.
            { simpl. right. left. reflexivity. }
            { apply prefix_rule. }
            { apply prefix_rule. }
          }
          apply empty_trace_rule.
        }
Qed.

Example TEAM_trace1_auto : traceR S_TEAM "TEAM" ["lift_piano"].
Proof. solve_trace. Qed.

Example TEAM_trace1' : extendedTraceR S_TEAM "TEAM" [Tau ; Tau ; Tau ; Tau; Event "lift_piano"].
Proof.
  unfold extendedTraceR. simpl.
  exists (ProcRef "PETE" [| {{"lift_piano", "lift_table"}} |] ProcRef "DAVE").
  apply sos_transitive_rule with
      (R := ("lift_piano" --> ProcRef "PETE" |~| "lift_table" --> ProcRef "PETE") [| {{"lift_piano", "lift_table"}} |] ProcRef "DAVE").
  - apply gener_parall_tau_indep_left_rule.
    * apply reference_rule with (name := "PETE").
      + reflexivity.
      + simpl. reflexivity.
  - apply sos_transitive_rule with 
      (R := ("lift_piano" --> ProcRef "PETE" |~| "lift_table" --> ProcRef "PETE")
            [| Alphabet {{"lift_piano", "lift_table"}} |]
            ("lift_piano" --> ProcRef "DAVE" |~| "lift_table" --> ProcRef "DAVE")).
    * apply gener_parall_tau_indep_right_rule.
      apply reference_rule with (name := "DAVE").
      + reflexivity.
      + simpl. reflexivity.
    * apply sos_transitive_rule with
        (R := "lift_piano" --> ProcRef "PETE" 
              [|Alphabet {{"lift_piano", "lift_table"}}|] 
              ("lift_piano" --> ProcRef "DAVE" |~| "lift_table" --> ProcRef "DAVE")).
      + apply gener_parall_tau_indep_left_rule.
        apply int_choice_left_rule.
      + apply sos_transitive_rule with
        (R := "lift_piano" --> ProcRef "PETE" [|Alphabet {{"lift_piano", "lift_table"}}|] "lift_piano" --> ProcRef "DAVE").
        { apply gener_parall_tau_indep_right_rule.
          apply int_choice_left_rule. 
        }
        { apply sos_transitive_rule with (R := ProcRef "PETE" [|Alphabet {{"lift_piano", "lift_table"}}|] ProcRef "DAVE").
          { apply gener_parall_joint_rule.
            { simpl. right. left. reflexivity. }
            { apply prefix_rule. }
            { apply prefix_rule. }
          }
          { apply sos_empty_rule. }
        }
Qed.

Example TEAM_trace2_auto : traceR S_TEAM "TEAM" ["lift_piano"; "lift_table"].
Proof. solve_trace. Qed.

Example TEAM_trace3_auto : traceR S_TEAM "PETE" ["lift_table" ; "lift_piano" ; "lift_piano" ; "lift_piano" ; "lift_table"].
Proof. solve_trace. Qed.

Definition LIGHT := "LIGHT" ::= "on" --> "off" --> ProcRef "LIGHT".
Definition S_LIGHT := Spec [Channel {{"on", "off"}}] [LIGHT].

Example LIGHT_trace1 : traceR S_LIGHT "LIGHT" ["on" ; "off" ; "on"].
Proof.
  unfold traceR. simpl. eapply event_trace_rule.
  - apply prefix_rule.
  - eapply event_trace_rule.
    * apply prefix_rule.
    * eapply tau_trace_rule.
      + apply reference_rule with (name := "LIGHT").
        { reflexivity. }
        { reflexivity. }
      + simpl. eapply event_trace_rule.
        { apply prefix_rule. }
        { apply empty_trace_rule. }
Qed.

Example LIGHT_trace1_auto : traceR S_LIGHT "LIGHT" ["on"; "off" ; "on"].
Proof. solve_trace. Qed.

Example LIGHT_trace1' : extendedTraceR S_LIGHT "LIGHT" [Event "on" ; Event "off" ; Tau ; Event "on"].
  unfold extendedTraceR. simpl.
  exists ("off" --> ProcRef "LIGHT").
  apply sos_transitive_rule with (R := "off" --> ProcRef "LIGHT").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := ProcRef "LIGHT").
    * apply prefix_rule.
    * apply sos_transitive_rule with (R := "on" --> "off" --> ProcRef "LIGHT").
      + apply reference_rule with (name := "LIGHT").
        { reflexivity. }
        { simpl. reflexivity. }
      + apply sos_transitive_rule with (R := "off" --> ProcRef "LIGHT").
        { apply prefix_rule. }
        { apply sos_empty_rule. }
Qed.
*)
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

Example FORECOURT_trace1 : traceR S_FORECOURT "FORECOURT"
    ["lift_nozzle_1" ; "lift_nozzle_2" ; "depress_trigger_1" ; "depress_trigger_2" ; "release_trigger_2"].
Proof.
  unfold traceR. simpl. eapply tau_trace_rule.
  - apply interleave_left_rule.
    * unfold not. intros. inversion H.
    * apply reference_rule with (name := "PUMP1").
      + reflexivity.
      + reflexivity.
  - simpl. eapply tau_trace_rule.
    * apply interleave_right_rule.
      + unfold not. intros. inversion H.
      + apply reference_rule with (name := "PUMP2").
        { reflexivity. }
        { reflexivity. }
    * simpl. eapply event_trace_rule.
      + apply interleave_left_rule.
        { unfold not. intros. inversion H. }
        { apply prefix_rule. }
      + eapply event_trace_rule.
        { 
          apply interleave_right_rule.
          { unfold not. intros. inversion H. }
          { apply prefix_rule. }
        }
        {
          eapply tau_trace_rule.
          {
            apply interleave_left_rule.
            { unfold not. intros. inversion H. }
            { apply reference_rule with (name := "READY1").
              { reflexivity. }
              { reflexivity. }
            }
          }
          simpl. eapply event_trace_rule.
          {
            apply interleave_left_rule.
            { unfold not. intros. inversion H. }
            {
              apply ext_choice_right_rule.
              { unfold not. intros. inversion H. }
              { apply prefix_rule. }
            }
          }
          eapply tau_trace_rule.
          {
            apply interleave_right_rule.
            { unfold not. intros. inversion H. }
            { 
              apply reference_rule with (name := "READY2").
              { reflexivity. }
              { reflexivity. }
            }
          }
          simpl. eapply event_trace_rule.
          {
            apply interleave_right_rule.
            { unfold not. intros. inversion H. }
            { 
              apply ext_choice_right_rule.
              { unfold not. intros. inversion H. }
              { apply prefix_rule. }
            }
          }
          eapply event_trace_rule.
          {
            apply interleave_right_rule.
            { unfold not. intros. inversion H. }
            { apply prefix_rule. }
          }
          apply empty_trace_rule. 
        }
Qed.

Example FORECOURT_trace1_auto : traceR S_FORECOURT "FORECOURT"
    ["lift_nozzle_1" ; "lift_nozzle_2" ; "depress_trigger_1" ; "depress_trigger_2" ; "release_trigger_2"].
Proof. solve_trace. Qed.

Example FORECOURT_trace1' : extendedTraceR S_FORECOURT "FORECOURT"
  [Tau ; Event "lift_nozzle_1" ; Tau ; Event "lift_nozzle_2" ; Tau ; Event "depress_trigger_1"
  ; Tau ; Event "depress_trigger_2" ; Event "release_trigger_2"].
Proof.
  unfold extendedTraceR.
  exists ("release_trigger_1" --> ProcRef "READY1" ||| ProcRef "READY2").
  apply sos_transitive_rule with (R := "lift_nozzle_1" --> ProcRef "READY1" ||| ProcRef "PUMP2").
    * apply interleave_left_rule.
      + unfold not. intro. inversion H.
      + apply reference_rule with (name := "PUMP1").
        { reflexivity. }
        { reflexivity. }
    * apply sos_transitive_rule with (R := ProcRef "READY1" ||| ProcRef "PUMP2").
      + apply interleave_left_rule.
        { intro. inversion H. }
        { apply prefix_rule. }
      + apply sos_transitive_rule with (R := ProcRef "READY1" ||| "lift_nozzle_2" --> ProcRef "READY2").
        { 
          apply interleave_right_rule.
          { intro. inversion H. }
          {
            apply reference_rule with (name := "PUMP2").
            { reflexivity. }
            { simpl. reflexivity. } 
          }
        }
        { 
          apply sos_transitive_rule with (R := ProcRef "READY1" ||| ProcRef "READY2").
          {
            apply interleave_right_rule.
            { intro. inversion H. }
            { apply prefix_rule. }
          }
          {
            apply sos_transitive_rule with
              (R := ("replace_nozzle_1" --> ProcRef "PUMP1"
                    [] "depress_trigger_1" --> "release_trigger_1" --> ProcRef "READY1") ||| ProcRef "READY2").
            {
              apply interleave_left_rule.
              { intro. inversion H. }
              {
                apply reference_rule with (name := "READY1").
                { reflexivity. }
                { simpl. reflexivity. }
              }
            }
            {
              apply sos_transitive_rule with (R := ("release_trigger_1" --> ProcRef "READY1") ||| ProcRef "READY2").
              {
                apply interleave_left_rule.
                { intro. inversion H. }
                {
                  apply ext_choice_right_rule.
                  { intro. inversion H. }
                  { apply prefix_rule. }
                }
              }
              {
                apply sos_transitive_rule with
                  (R := "release_trigger_1" --> ProcRef "READY1"
                        ||| ("replace_nozzle_2" --> ProcRef "PUMP2"
                            [] "depress_trigger_2" --> "release_trigger_2" --> ProcRef "READY2")).
                {
                  apply interleave_right_rule.
                  { intro. inversion H. }
                  {
                    apply reference_rule with (name := "READY2").
                    { reflexivity. }
                    { simpl. reflexivity. }
                  }
                }
                {
                  apply sos_transitive_rule with
                    (R := "release_trigger_1" --> ProcRef "READY1" ||| "release_trigger_2" --> ProcRef "READY2").
                  {
                    apply interleave_right_rule.
                    { intro. inversion H. }
                    {
                      apply ext_choice_right_rule.
                      { intro. inversion H. }
                      { apply prefix_rule. }
                    }
                  }
                  {
                    apply sos_transitive_rule with (R := "release_trigger_1" --> ProcRef "READY1" ||| ProcRef "READY2").
                    {
                      apply interleave_right_rule. 
                      { intro. inversion H. }
                      { apply prefix_rule. }
                    }
                    apply sos_empty_rule.
                  }
                }
              }
            }
          }
        }
Qed.

Example FORECOURT_trace2_auto : traceR S_FORECOURT "FORECOURT"
  ["lift_nozzle_1" ; "lift_nozzle_2" ; "depress_trigger_1" ; "depress_trigger_2" ; "release_trigger_2"
  ; "release_trigger_1" ; "replace_nozzle_2" ; "replace_nozzle_1" ; "lift_nozzle_2"].
Proof. solve_trace. Qed.

Definition SPY := "SPY" ::= "listen" --> "relay" --> ProcRef "SPY".
Definition MASTER := "MASTER" ::= "relay" --> "log" --> ProcRef "MASTER".
Definition MASTER_SPY := "MASTER_SPY" ::= ProcRef "SPY" [| {{"relay"}} |] ProcRef "MASTER" \ {{"relay"}}.
Definition S_MASTER_SPY := Spec [Channel {{"listen", "relay", "log"}}] [SPY ; MASTER ; MASTER_SPY].

Example MASTER_SPY_trace1 : traceR S_MASTER_SPY "MASTER_SPY" ["listen" ; "log"].
Proof.
  unfold traceR; simpl. eapply tau_trace_rule.
  - eapply hiding_tau_tick_rule.
    + left. reflexivity.
    + eapply gener_parall_tau_indep_left_rule. eapply reference_rule; reflexivity.
  - eapply tau_trace_rule.
    + eapply hiding_tau_tick_rule.
      * left. reflexivity.
      * eapply gener_parall_tau_indep_right_rule. eapply reference_rule; reflexivity.
    + eapply event_trace_rule.
      * eapply hiding_not_hidden_rule.
        { simpl. unfold not. intros. destruct H; inversion H. }
        {
          eapply gener_parall_indep_left_rule.
          { simpl. unfold not. intros. destruct H; inversion H. }
          { apply prefix_rule. }
        }
      * eapply tau_trace_rule.
        {
          eapply hiding_rule.
          { simpl. left. reflexivity. }
          {
            eapply gener_parall_joint_rule; try apply prefix_rule.
            { simpl; left; reflexivity. }
          }
        }
        {
          eapply event_trace_rule.
          {
            eapply hiding_not_hidden_rule.
            { simpl. unfold not. intros. destruct H; inversion H. }
            eapply gener_parall_indep_right_rule.
            { simpl. unfold not. intros. destruct H; inversion H. }
            { apply prefix_rule. }
          }
          { apply empty_trace_rule. }
        }
Qed.

Example MASTER_SPY_trace1_auto : traceR S_MASTER_SPY "MASTER_SPY" ["listen" ; "log"].
Proof. solve_trace. Qed.

Example MASTER_SPY_trace2_auto : traceR S_MASTER_SPY "MASTER_SPY" ["listen" ; "listen" ; "log" ; "listen" ; "log"].
Proof. solve_trace. Qed.

Definition S_PURCHASE := Spec 
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
  ].
Example PURCHASE_trace : traceR S_PURCHASE "PURCHASE" ["select" ; "return" ; "select" ; "keep"
  ; "card" ; "swipe" ; "reject" ; "cash" ; "receipt"].
Proof. solve_trace. Qed.

Definition TICKET := "TICKET" ::= "cash" --> "ticket" --> ProcRef "TICKET".
Definition CHANGE := "CHANGE" ::= "cash" --> "change" --> ProcRef "CHANGE".
Definition MACHINE :=
  "MACHINE" ::= ProcRef "TICKET" [[ {{"cash", "ticket"}} \\ {{"cash", "change"}} ]] ProcRef "CHANGE".
Definition PARKING_PERMIT_MCH := Spec [Channel {{"cash", "ticket", "change"}}] [TICKET ; CHANGE ; MACHINE].

Example PARKING_trace : traceR PARKING_PERMIT_MCH "MACHINE" ["cash" ; "ticket" ; "change" ; "cash" ; "change" ; "ticket"].
Proof. solve_trace. Qed.

Definition TOY_PROBLEM := Spec [Channel {{"a", "b"}}] [("P" ::= "a" --> STOP) ; ("Q" ::= "a" --> "b" --> STOP)
  ; ("R" ::= ProcRef "P" [] ProcRef "Q")].
Example TOY_PROBLEM_trace : traceR TOY_PROBLEM "R" ["a" ; "b"].
Proof. solve_trace. Qed.

Theorem extended_to_trace :
  forall (C : specification) (P : string) (exT : extendedTrace),
    extendedTraceR C P exT -> traceR C P (get_trace exT).
Proof. Admitted.

Theorem trace_to_extended :
  forall (C : specification) (P : string) (t : trace),
    traceR C P t ->
    exists (exT : extendedTrace),
      t = get_trace exT /\ extendedTraceR C P exT.
Proof. Admitted.

Local Close Scope string.