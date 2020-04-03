Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Open Scope string_scope.

(** TYPE DEFINITIONS **)

Notation event := string.

Inductive event_tau_tick :=
  | Event (e : event)
  | Tau
  | Tick.

Inductive alphabet : Type :=
  | Alphabet (events : set event).

Inductive channel : Type :=
  | Channel (events : set event).

Inductive proc_body : Type :=
  | SKIP
  | STOP
  | ProcRef (name : string)
  | ProcPrefix (event : event) (proc : proc_body)
  | ProcExtChoice (proc1 proc2 : proc_body)
  | ProcIntChoice (proc1 proc2 : proc_body)
  | ProcAlphaParallel (proc1 proc2 : proc_body) (alph1 alph2 : alphabet)
  | ProcGenParallel (proc1 proc2 : proc_body) (alph : alphabet)
  | ProcInterleave (proc1 proc2 : proc_body)
  | ProcSeqComp (proc1 proc2 : proc_body).

Inductive proc_def : Type :=
  | Proc (name : string) (body : proc_body).

Inductive specification : Type :=
  | Spec (ch_list : list channel) (proc_list : list proc_def).

Fixpoint find_proc_body (proc_list : list proc_def) (proc_name : string) : proc_body :=
  match proc_list with
  | [] => STOP
  | (Proc name body) :: tail => match eqb proc_name name with
                                | true => body
                                | false => find_proc_body tail proc_name
                                end
  end.

Definition get_proc_body (context : specification) (proc_name : string) : proc_body :=
  match context with
  | Spec ch_list proc_list => find_proc_body proc_list proc_name
  end.

(** NOTATIONS/COERCIONS **) 

Definition event_dec := string_dec.

(* Notations for declaring sets of events. *)
Notation "{{ }}" := (empty_set event) (format "{{ }}").
Notation "{{ x }}" := (set_add event_dec x (empty_set event)).
Notation "{{ x , y , .. , z }}" := (set_add event_dec x (set_add event_dec y
    .. (set_add event_dec z (empty_set event)) ..)).

(* Coercion: alphabet to (event) set. *)
Definition alphabet_to_set (s : alphabet) : set event :=
  match s with
  | Alphabet b => b
  end.
Coercion alphabet_to_set : alphabet >-> set.

(* Process reference (coercion). *)
Definition str_to_proc_body (s : string) : proc_body := ProcRef s.
Coercion str_to_proc_body : string >-> proc_body.
(* Process definition *)
Notation "P ::= Q" := (Proc P Q) (at level 100).
(* Prefix *)
Notation "a --> P" := (ProcPrefix a P) (at level 80, right associativity).
(* External Choice *)
Notation "P [] Q" := (ProcExtChoice P Q) (at level 90, left associativity).
(* Internal Choice *)
Notation "P |~| Q" := (ProcIntChoice P Q) (at level 90, left associativity).
(* Alphabetised Parallel *)
Notation "P [[ A \\ B ]] Q" := (ProcAlphaParallel P Q A B) (at level 90, no associativity).
(* Generalised (or Interface) Parallel *)
Notation "P [| A |] Q" := (ProcGenParallel P Q A) (at level 90, no associativity).
(* Interleaving *)
Notation "P ||| Q" := (ProcInterleave P Q) (at level 90, left associativity).
(* Sequencial Composition *)
Notation "P ;; Q" := (ProcSeqComp P Q) (at level 90, left associativity).

(* Example 3.20 (book) using notations. *)
Definition SPurchase := 
  (
    Spec
    [
      Channel {{"select", "keep", "return"}}
      ; Channel {{"cash", "cheque", "card"}}
      ; Channel {{"swipe", "sign"}}
      ; Channel {{"receipt", "reject"}}
    ]

    [
      "CHOOSE" ::= "select" --> ("keep" --> SKIP 
                                [] "return" --> "CHOOSE")
      ; "PAY" ::= "cash" --> "receipt" --> SKIP
                  [] "cheque" --> "receipt" --> SKIP
                  [] "card" --> "swipe" --> ("sign" --> "receipt" --> SKIP
                                            [] "reject" --> "PAY")
      ; "PURCHASE" ::= "CHOOSE" ;; "PAY"
    ]
  ).

Reserved Notation "C '#' P '//' a '==>' Q" (at level 150, left associativity).
Inductive sosR : specification -> proc_body -> event_tau_tick -> proc_body -> Prop :=
  (* Prefix *)
  | prefix_rule (C : specification) (P Q : proc_body) (a : event) :
      C # (a --> P) // Event a ==> Q
  (* Reference *)
  (* This inference rule is different from the one implemented in the FDR tool. This approach will
    allow an ill-formed recursion such as P = P to be defined, by introducing a transition which communicates
    the internal event tau and, therefore, increasing the process LTS size. *)
  | reference_rule (C : specification) (P : proc_body) (name : string) :
      forall (Q : proc_body) (a : event_tau_tick),
      eq P (ProcRef name) ->
      (C # (get_proc_body C name) // Tau ==> Q) ->
      C # P // Tau ==> Q
  (* External Choice *)
  | ext_choice_left_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
      ~ eq a Tau ->
      (C # P // a ==> P') ->
      (C # P [] Q // a ==> P')
  | ext_choice_right_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
      ~ eq a Tau ->
      (C # P // a ==> P') ->
      (C # Q [] P // a ==> P')
  | ext_choice_tau_left_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body),
      (C # P // Tau ==> P') ->
      (C # P [] Q // Tau ==> P' [] Q)
  | ext_choice_tau_right_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body),
      (C # P // Tau ==> P') ->
      (C # Q [] P // Tau ==> Q [] P')
  (* Internal Choice *)
  | int_choice_left_rule (C : specification) (P Q : proc_body) :
      C # P |~| Q // Tau ==> P
  | int_choice_right_rule (C : specification) (P Q : proc_body) :
      C # Q |~| P // Tau ==> P
  (* Alphabetised Parallel *)
  | alpha_parall_indep_left_rule (C : specification) (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body) (a : event),
      set_In a (set_diff event_dec A B) ->
      (C # P // Event a ==> P') ->
      C # P [[ A \\ B ]] Q // Event a ==> P' [[ A \\ B ]] Q
  | alpha_parall_indep_right_rule (C : specification) (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body) (a : event),
      set_In a (set_diff event_dec A B) ->
      (C # P // Event a ==> P') ->
      C # Q [[ B \\ A ]] P // Event a ==> Q [[ B \\ A ]] P'
  | alpha_parall_tau_indep_left_rule (C : specification) (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body),
      (C # P // Tau ==> P') ->
      C # P [[ A \\ B ]] Q // Tau ==> P' [[ A \\ B ]] Q
  | alpha_parall_tau_indep_right_rule (C : specification) (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body),
      (C # P // Tau ==> P') ->
      C # Q [[ B \\ A ]] P // Tau ==> Q [[ B \\ A ]] P'
  | alpha_parall_joint_rule (C : specification) (P Q : proc_body) (A B : alphabet) :
      forall (P' Q' : proc_body) (a : event),
      set_In a (set_inter event_dec A B) ->
      (C # P // Event a ==> P') ->
      (C # Q // Event a ==> Q') ->
      C # P [[ A \\ B ]] Q // Event a ==> P' [[ A \\ B ]] Q'
  | alpha_parall_tick_joint_rule (C : specification) (P Q : proc_body) (A B : alphabet) :
      forall (P' Q' : proc_body),
      (C # P // Tick ==> P') ->
      (C # Q // Tick ==> Q') ->
      C # P [[ A \\ B ]] Q // Tick ==> P' [[ A \\ B ]] Q'
  (* Generalised Parallel *)
  | gener_parall_indep_left_rule (C : specification) (P Q : proc_body) (A : alphabet) :
      forall (P' : proc_body) (a : event),
      ~ set_In a A ->
      (C # P // Event a ==> P') ->
      C # P [| A |] Q // Event a ==> P' [| A |] Q
  | gener_parall_indep_right_rule (C : specification) (P Q : proc_body) (A : alphabet) :
      forall (P' : proc_body) (a : event),
      ~ set_In a A ->
      (C # P // Event a ==> P') ->
      C # Q [| A |] P // Event a ==> Q [| A |] P'
  | gener_parall_tau_indep_left_rule (C : specification) (P Q : proc_body) (A : alphabet) :
      forall (P' : proc_body),
      (C # P // Tau ==> P') ->
      C # P [| A |] Q // Tau ==> P' [| A |] Q
  | gener_parall_tau_indep_right_rule (C : specification) (P Q : proc_body) (A : alphabet) :
      forall (P' : proc_body),
      (C # P // Tau ==> P') ->
      C # Q [| A |] P // Tau ==> Q [| A |] P'
  | gener_parall_joint_rule (C : specification) (P Q : proc_body) (A : alphabet) :
      forall (P' Q' : proc_body) (a : event),
      set_In a A ->
      (C # P // Event a ==> P') ->
      (C # Q // Event a ==> Q') ->
      C # P [| A |] Q // Event a ==> P' [| A |] Q'
  | gener_parall_tick_joint_rule (C : specification) (P Q : proc_body) (A : alphabet) :
      forall (P' Q' : proc_body),
      (C # P // Tick ==> P') ->
      (C # Q // Tick ==> Q') ->
      C # P [| A |] Q // Tick ==> P' [| A |] Q'
  (* Interleave *)
  | interleave_left_rule (P Q : proc_body) :
      forall (C : specification) (P' : proc_body) (a : event_tau_tick),
      ~ eq a Tick ->
      (C # P // a ==> P') ->
      C # P ||| Q // a ==> P' ||| Q
  | interleave_right_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
      ~ eq a Tick ->
      (C # P // a ==> P') ->
      C # Q ||| P // a ==> Q ||| P'
  | interleave_tick_rule (C : specification) (P Q : proc_body) :
      forall (P' Q' : proc_body),
      (C # P // Tick ==> P') ->
      (C # Q // Tick ==> Q') ->
      C # P ||| Q // Tick ==> P' ||| Q'
  (* Sequential Composition *)
  (* This inference rule is different from the one implemented in the FDR tool. The main consequence
    of this approach is that the transition resulting from the communication of the internal event tau
    will not be supressed and, therefore, will appear in the LTS. *)
  | seq_comp_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
      ~ eq a Tick ->
      (C # P // a ==> P') ->
      C # P ;; Q // a ==> P' ;; Q
  | seq_comp_tick_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body),
      (C # P // Tick ==> P') ->
      C # P ;; Q // Tau ==> Q
  where "C '#' P '//' a '==>' Q" := (sosR C P a Q).

Reserved Notation "C '#' P '///' t '==>' Q" (at level 150, left associativity).
Inductive sosStarR : specification -> proc_body -> list event_tau_tick -> proc_body -> Prop :=
  | sos_empty_rule (C : specification) (P : proc_body) :
      C # P /// nil ==> P
  | sos_transitive_rule (C : specification) (P R Q : proc_body) (head : event_tau_tick) (tail : list event_tau_tick) :
      (C # P // head ==> R) -> (C # R /// tail ==> Q) -> (C # P /// (head :: tail) ==> Q)
  where "C '#' P '///' t '==>' Q" := (sosStarR C P t Q).
  
Definition traceBodyR (C : specification) (body : proc_body) (t : list event_tau_tick) :=
  exists (body' : proc_body), C # body /// t ==> body'.
  
Definition traceR (C : specification) (P : proc_def) (t : list event_tau_tick) :=
  match P with
  | Proc name body => traceBodyR C body t
  end.

(** TRACE EXAMPLES **)

Definition CH_PRINTER0 := Channel {{"accept", "print"}}.
Definition PRINTER0 := "PRINTER0" ::= "accept" --> "print" --> STOP.
Definition S_PRINTER0 := Spec [CH_PRINTER0] [PRINTER0].

Example PRINTER0_empty_trace : traceR S_PRINTER0 PRINTER0 nil.
Proof.
  unfold traceR. simpl.
  exists ("accept" --> "print" --> STOP).
  apply sos_empty_rule.
Qed.

Example PRINTER0_trace1 : traceR S_PRINTER0 PRINTER0 [Event "accept"].
Proof.
  unfold traceR. simpl.
  exists ("print" --> STOP).
  apply sos_transitive_rule with (R := "print" --> STOP).
  - apply prefix_rule.
  - apply sos_empty_rule.
Qed.

Example PRINTER0_trace2 : traceR S_PRINTER0 PRINTER0 [Event "accept" ; Event "print"].
Proof.
  unfold traceR. simpl.
  exists (STOP).
  apply sos_transitive_rule with (R := "print" --> STOP).
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := STOP).
    + apply prefix_rule.
    + apply sos_empty_rule.
Qed.

Example PRINTER0_trace2' : traceR S_PRINTER0 PRINTER0 [Event "accept" ; Event "print"].
Proof.
  unfold traceR. simpl.
  exists (STOP).
  eapply sos_transitive_rule.
  - apply prefix_rule.
  - eapply sos_transitive_rule.
    + apply prefix_rule.
    + apply sos_empty_rule.
  Unshelve. exact SKIP.
Qed.

Definition CH_CHOOSE := Channel {{"select", "keep", "return"}}.
Definition P_CHOOSE := "CHOOSE" ::= "select" --> ("keep" --> SKIP
                                                [] "return" --> "CHOOSE").
Definition S_CHOOSE := Spec [CH_CHOOSE] [P_CHOOSE].
Example CHOOSE_trace1 : traceR S_CHOOSE P_CHOOSE [Event "select" ; Event "keep"].
Proof.
  unfold traceR. simpl.
  exists (SKIP).
  apply sos_transitive_rule with (R := "keep" --> SKIP [] "return" --> "CHOOSE").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := SKIP).
    * apply ext_choice_left_rule.
      + unfold not. intro. inversion H.
      + apply prefix_rule.
    * apply sos_empty_rule.
Qed.

Example CHOOSE_trace2 : traceR S_CHOOSE P_CHOOSE [Event "select" ; Event "return"].
Proof.
  unfold traceR. simpl.
  exists ("CHOOSE").
  apply sos_transitive_rule with (R := "keep" --> SKIP [] "return" --> "CHOOSE").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := "CHOOSE").
    * apply ext_choice_right_rule.
      + unfold not. intro. inversion H.
      + apply prefix_rule.
    * apply sos_empty_rule.
Qed.

Definition CH_TEAM := Channel {{"lift_piano", "lift_table"}}.
Definition PETE := "PETE" ::= "lift_piano" --> "PETE"
                              |~| "lift_table" --> "PETE".

Definition DAVE := "DAVE" ::= "lift_piano" --> "DAVE"
                              |~| "lift_table" --> "DAVE".

Definition TEAM := "TEAM" ::= "PETE" [| Alphabet {{"lift_piano", "lift_table"}} |] "DAVE".

Definition S_TEAM := Spec [CH_TEAM] [PETE ; DAVE ; TEAM].

Example TEAM_trace1 : traceR S_TEAM TEAM [Tau ; Event "lift_piano"].
Proof.
  unfold traceR. simpl.
  exists ("PETE" [| Alphabet {{"lift_piano", "lift_table"}} |] "DAVE").
  apply sos_transitive_rule with (R := "lift_piano" --> "PETE" [| Alphabet {{"lift_piano", "lift_table"}} |] "lift_piano" --> "DAVE").
  - apply gener_parall_joint_rule.
    * apply reference_rule with (name := "PETE").
      + reflexivity.
      + simpl. apply int_choice_left_rule.
    * apply reference_rule with (name := "DAVE").
      + reflexivity.
      + simpl. apply int_choice_left_rule.
  - apply sos_transitive_rule with (R := "PETE" [|Alphabet {{"lift_piano", "lift_table"}}|] "DAVE").
    * apply gener_parall_joint_rule.
      + apply prefix_rule.
      + apply prefix_rule.
    * apply sos_empty_rule.
Qed.

Definition LIGHT := "LIGHT" ::= "on" --> "off" --> "LIGHT".
Definition S_LIGHT := Spec [Channel {{"on", "off"}}] [LIGHT].

Example LIGHT_trace1 : traceR S_LIGHT LIGHT [Event "on" ; Event "off" ; Event "on"].
Proof.
  unfold traceR. simpl.
  exists ("off" --> "LIGHT").
  apply sos_transitive_rule with (R := "off" --> "LIGHT").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := "on" --> "off" --> "LIGHT").
    * apply prefix_rule.
    * apply sos_transitive_rule with (R := "off" --> "LIGHT").
      + apply prefix_rule.
      + apply sos_empty_rule.
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

Example FORECOURT_trace1 : traceR S_FORECOURT ("FORECOURT" ::= "PUMP1" ||| "PUMP2")
    [Event "lift_nozzle_1" ; Event "depress_trigger_1" ; Event "lift_nozzle_2"
    ; Event "depress_trigger_2" ; Event "release_trigger_2"].
Proof.
  unfold traceR. simpl.
  exists("release_trigger_1" --> "READY1" ||| "READY2").
  apply sos_transitive_rule with (R := "READY1" ||| "PUMP2").
  - apply interleave_left_rule. apply reference_rule with (name := "PUMP1").
    * reflexivity.
    * simpl. apply prefix_rule.
  - apply sos_transitive_rule with (R := "release_trigger_1" --> "READY1" ||| "PUMP2").
    * apply interleave_left_rule. apply reference_rule with (name := "READY1").
      + reflexivity.
      + simpl. apply ext_choice_right_rule. apply prefix_rule.
    * apply sos_transitive_rule with (R := "release_trigger_1" --> "READY1" ||| "READY2").
      + apply interleave_right_rule. apply reference_rule with (name := "PUMP2").
          { reflexivity. }
          { simpl. apply prefix_rule. }
      + apply sos_transitive_rule with (R := "release_trigger_1" --> "READY1" ||| "release_trigger_2" --> "READY2").
        { 
          apply interleave_right_rule. apply reference_rule with (name := "READY2").
          { reflexivity. }
          { simpl. apply ext_choice_right_rule. apply prefix_rule. }
        }
        { 
          apply sos_transitive_rule with (R := "release_trigger_1" --> "READY1" ||| "READY2").
          { apply interleave_right_rule. apply prefix_rule. }
          { apply sos_empty_rule. }
        }
Qed.
