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

(** TRACE EXAMPLES **)

Local Open Scope string.
(* 
Definition CH_PRINTER0 := Channel {{"accept", "print"}}.
Definition PRINTER0 := "PRINTER0" ::= "accept" --> "print" --> STOP.
Definition S_PRINTER0 := Spec [CH_PRINTER0] [PRINTER0].

Example PRINTER0_empty_trace : traceR S_PRINTER0 "PRINTER0" nil.
Proof.
  unfold traceR. simpl.
  apply empty_trace_rule.
Qed.

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
(*
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

Example CHOOSE_trace1' : extendedTraceR S_CHOOSE "CHOOSE" [Event "select" ; Event "keep"].
Proof.
  unfold extendedTraceR. simpl. eexists.
  apply sos_transitive_rule with (R := "keep" --> SKIP [] "return" --> "CHOOSE").
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
*)
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

Example TEAM_trace1' : extendedTraceR S_TEAM "TEAM" [Tau ; Tau ; Tau ; Tau; Event "lift_piano"].
Proof.
  unfold extendedTraceR. simpl.
  exists ("PETE" [| {{"lift_piano", "lift_table"}} |] "DAVE").
  apply sos_transitive_rule with
      (R := ("lift_piano" --> "PETE" |~| "lift_table" --> "PETE") [| {{"lift_piano", "lift_table"}} |] "DAVE").
  - apply gener_parall_tau_indep_left_rule.
    * apply reference_rule with (name := "PETE").
      + reflexivity.
      + simpl. reflexivity.
  - apply sos_transitive_rule with 
      (R := ("lift_piano" --> "PETE" |~| "lift_table" --> "PETE")
            [| Alphabet {{"lift_piano", "lift_table"}} |]
            ("lift_piano" --> "DAVE" |~| "lift_table" --> "DAVE")).
    * apply gener_parall_tau_indep_right_rule.
      apply reference_rule with (name := "DAVE").
      + reflexivity.
      + simpl. reflexivity.
    * apply sos_transitive_rule with
        (R := "lift_piano" --> "PETE" 
              [|Alphabet {{"lift_piano", "lift_table"}}|] 
              ("lift_piano" --> "DAVE" |~| "lift_table" --> "DAVE")).
      + apply gener_parall_tau_indep_left_rule.
        apply int_choice_left_rule.
      + apply sos_transitive_rule with
        (R := "lift_piano" --> "PETE" [|Alphabet {{"lift_piano", "lift_table"}}|] "lift_piano" --> "DAVE").
        { apply gener_parall_tau_indep_right_rule.
          apply int_choice_left_rule. 
        }
        { apply sos_transitive_rule with (R := "PETE" [|Alphabet {{"lift_piano", "lift_table"}}|] "DAVE").
          { apply gener_parall_joint_rule.
            { simpl. right. left. reflexivity. }
            { apply prefix_rule. }
            { apply prefix_rule. }
          }
          { apply sos_empty_rule. }
        }
Qed.
*)

Definition LIGHT := "LIGHT" ::= "on" --> "off" --> ProcRef "LIGHT".
Definition S_LIGHT := Spec [Channel {{"on", "off"}}] [LIGHT].

(* 
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

Example LIGHT_trace1' : extendedTraceR S_LIGHT "LIGHT" [Event "on" ; Event "off" ; Tau ; Event "on"].
  unfold extendedTraceR. simpl.
  exists ("off" --> "LIGHT").
  apply sos_transitive_rule with (R := "off" --> "LIGHT").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := "LIGHT").
    * apply prefix_rule.
    * apply sos_transitive_rule with (R := "on" --> "off" --> "LIGHT").
      + apply reference_rule with (name := "LIGHT").
        { reflexivity. }
        { simpl. reflexivity. }
      + apply sos_transitive_rule with (R := "off" --> "LIGHT").
        { apply prefix_rule. }
        { apply sos_empty_rule. }
Qed.

Definition S_FORECOURT :=
  (
    Spec
    [
      Channel {{"lift_nozzle_1", "replace_nozzle_1", "depress_trigger_1", "release_trigger_1"}}
      ; Channel {{"lift_nozzle_2", "replace_nozzle_2", "depress_trigger_2", "release_trigger_2"}}
    ]
    [
      "PUMP1" ::= "lift_nozzle_1" --> "READY1"
      ; "READY1" ::= "replace_nozzle_1" --> "PUMP1"
                      [] "depress_trigger_1" --> "release_trigger_1" --> "READY1"
      ; "PUMP2" ::= "lift_nozzle_2" --> "READY2"
      ; "READY2" ::= "replace_nozzle_2" --> "PUMP2"
                      [] "depress_trigger_2" --> "release_trigger_2" --> "READY2"
      ; "FORECOURT" ::= "PUMP1" ||| "PUMP2"
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

Example FORECOURT_trace1' : extendedTraceR S_FORECOURT "FORECOURT"
  [Tau ; Event "lift_nozzle_1" ; Tau ; Event "lift_nozzle_2" ; Tau ; Event "depress_trigger_1"
  ; Tau ; Event "depress_trigger_2" ; Event "release_trigger_2"].
Proof.
  unfold extendedTraceR.
  exists ("release_trigger_1" --> "READY1" ||| "READY2").
  apply sos_transitive_rule with (R := "lift_nozzle_1" --> "READY1" ||| "PUMP2").
    * apply interleave_left_rule.
      + unfold not. intro. inversion H.
      + apply reference_rule with (name := "PUMP1").
        { reflexivity. }
        { reflexivity. }
    * apply sos_transitive_rule with (R := "READY1" ||| "PUMP2").
      + apply interleave_left_rule.
        { intro. inversion H. }
        { apply prefix_rule. }
      + apply sos_transitive_rule with (R := "READY1" ||| "lift_nozzle_2" --> "READY2").
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
          apply sos_transitive_rule with (R := "READY1" ||| "READY2").
          {
            apply interleave_right_rule.
            { intro. inversion H. }
            { apply prefix_rule. }
          }
          {
            apply sos_transitive_rule with
              (R := ("replace_nozzle_1" --> "PUMP1"
                    [] "depress_trigger_1" --> "release_trigger_1" --> "READY1") ||| "READY2").
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
              apply sos_transitive_rule with (R := ("release_trigger_1" --> "READY1") ||| "READY2").
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
                  (R := "release_trigger_1" --> "READY1"
                        ||| ("replace_nozzle_2" --> "PUMP2"
                            [] "depress_trigger_2" --> "release_trigger_2" --> "READY2")).
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
                    (R := "release_trigger_1" --> "READY1" ||| "release_trigger_2" --> "READY2").
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
                    apply sos_transitive_rule with (R := "release_trigger_1" --> "READY1" ||| "READY2").
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
*)

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

(* TODO Finish this tactic macro. (Would it be easier to solve for extendedTraceR instead of traceR?) *)
Ltac solve_trace := unfold traceR; simpl;
  repeat (
    match goal with
    (* Empty trace *)
    | |- traceR' _ _ nil => apply empty_trace_rule
    (* Non-empty trace *)
    | |- traceR' _ ?P (?h :: _) =>
      match P with
      (* Prefix *)
      | h --> _  => eapply event_trace_rule
      (* Process unfolding *)
      | ProcRef _ => eapply tau_trace_rule
      (* External choice *)
      | h --> _ [] _ => eapply event_trace_rule
      | _ [] h --> _ => eapply event_trace_rule
      | ProcRef _ [] _ => eapply tau_trace_rule
      | _ [] ProcRef _ => eapply tau_trace_rule
      (* Internal choice *)
      | h --> ?Q |~| _ => apply tau_trace_rule with (P' := h --> Q)
      | _ |~| h --> ?Q => apply tau_trace_rule with (P' := h --> Q)
      | _ |~| _ => eapply tau_trace_rule
      (* Interleaving *)
      | h --> ?Q ||| ?Q' => apply event_trace_rule with (P' := ?Q ||| ?Q')
      | ?Q ||| h --> ?Q' => apply event_trace_rule with (P' := ?Q ||| ?Q')
      end
    (* SOS Prefix rule *)
    | |- (_ # (?e --> _) // Event ?e ==> _) => apply prefix_rule
    (* SOS Reference rule *)
    | |- (_ # (ProcRef _) // Tau ==> _) => eapply reference_rule
    (* SOS External choice rule *)
    | |- (_ # (?e --> _) [] _ // Event ?e ==> _) => eapply ext_choice_left_rule
    | |- (_ # _ [] (?e --> _) // Event ?e ==> _) => eapply ext_choice_right_rule
    (* SOS Internal choice *)
    | |- (_ # ?P |~| ?Q // Tau ==> ?P) => eapply int_choice_left_rule
    | |- (_ # ?P |~| ?Q // Tau ==> ?Q) => eapply int_choice_right_rule
    (* SOS Interleaving *)
    | |- (_ # ?e --> ?P ||| ?Q // Event ?e ==> ?P ||| ?Q) => eapply interleave_left_rule
    | |- (_ # ?P ||| ?e --> ?Q // Event ?e ==> ?P ||| ?Q) => eapply interleave_right_rule
    (* Prove not equal *)
    | |- _ <> _ => unfold not; let H := fresh "H" in intros H; inversion H
    (* Prove equal *)
    | |- _ = _ => reflexivity
    (* None of the above *)
    | |- _ => fail
    end).

Example CHOOSE_trace1 : traceR S_CHOOSE "CHOOSE" ["select" ; "return" ; "select" ; "keep"].
Proof.
  solve_trace.
Qed.

Example LIGHT_trace2 : traceR S_LIGHT "LIGHT" ["on"; "off" ; "on"].
Proof.
  solve_trace.
Qed.

Example TEAM_trace1 : traceR S_TEAM "PETE" ["lift_piano" ; "lift_table"].
Proof.
  solve_trace.
Qed.

Theorem extended_to_trace :
  forall (C : specification) (P : string) (exT : extendedTrace),
    extendedTraceR C P exT -> traceR C P (get_trace exT).
Proof. Admitted.

Theorem trace_to_extended :
  forall (C : specification) (P : string) (t : trace),
    traceR C P t ->
    exists (exT : extendedTrace),
      t = get_trace exT /\ extendedTraceR C P exT.
Proof.
  intros.
  - destruct C. induction t.
    * exists nil. split.
      + reflexivity.
      + destruct P, proc_list; try inversion H.
        {
          destruct p, name.
          { 
            unfold extendedTraceR; simpl. unfold extendedTraceR'.
            exists body. apply sos_empty_rule.
          } Admitted.

Local Close Scope string.