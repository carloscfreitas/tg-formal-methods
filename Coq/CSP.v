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
  | ProcRef (name : string) (* A reference to a process. May be itself (recursion). *)
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
Notation "{{ x , y , .. , z }}" := (set_add event_dec x (set_add event_dec y .. (set_add event_dec z (empty_set event)) ..)).

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
(* Alphabetised Parallel (TODO Still not working...) *)
Notation "P [[ A || B ]] Q" := (ProcAlphaParallel P Q A B) (at level 90, no associativity).
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

Compute get_proc_body SPurchase "PURCHASE".

(* TODO Add context (specification) to this type.
  Revisit the transition rules bellow and check their alphabet. *)
Reserved Notation "P '//' a '==>' Q" (at level 150, left associativity).
Inductive sosR : proc_body -> event_tau_tick -> proc_body -> Prop :=
  (* Prefix *)
  | prefix_rule (P Q : proc_body) (a : event) :
      (a --> P) // Event a ==> Q
  (* Reference *)
  | reference_rule (P : proc_body) (name : string) :
      eq P (ProcRef name) -> P // Tau ==> P (*TODO (get_proc_body spec name) *)
  (* External Choice *)
  | ext_choice_left_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> (P [] Q // Event a ==> P')
  | ext_choice_right_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> (Q [] P // Event a ==> P')
  (* Internal Choice. TODO This definition is not working properly. *)
  | int_choice_left_rule (P Q : proc_body) :
      forall (tau : string), P |~| Q // Tau ==> P
  | int_choice_right_rule (P Q : proc_body) (tau : string) :
      forall (tau : string), P |~| Q // Tau ==> Q
  (* Alphabetised Parallel *)
  | alpha_parall_indep_left_rule (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> (ProcAlphaParallel P Q A B) // Event a ==> (ProcAlphaParallel P' Q A B)
  | alpha_parall_indep_right_rule (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> (ProcAlphaParallel Q P A B) // Event a ==> (ProcAlphaParallel Q P' A B)
  | alpha_parall_joint_rule (P Q : proc_body) (A B : alphabet) :
      forall (P' Q' : proc_body) (a : event), (P // Event a ==> P') -> (Q // Event a ==> Q') -> (ProcAlphaParallel P Q A B) // Event a ==> (ProcAlphaParallel P' Q' A B)
  (* Generalised Parallel *)
  | gener_parall_indep_left_rule (P Q : proc_body) (A : alphabet) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> P [| A |] Q // Event a ==> P' [| A |] Q
  | gener_parall_indep_right_rule (P Q : proc_body) (A : alphabet) :
    forall (P' : proc_body) (a : event), (P // Event a ==> P') -> Q [| A |] P // Event a ==> Q [| A |] P'
  | gener_parall_joint_rule (P Q : proc_body) (A : alphabet) :
      forall (P' Q' : proc_body) (a : event), (P // Event a ==> P') -> (Q // Event a ==> Q') -> P [| A |] Q // Event a ==> P' [| A |] Q'
  (* Interleave *)
  | interleave_left_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> P ||| Q // Event a ==> P' ||| Q
  | interleave_right_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> Q ||| P // Event a ==> Q ||| P'
  | interleave_tick_rule (P Q : proc_body) :
      (* TODO Check if there is indeed a conjuction in this transition rule. *)
      forall (P' Q' : proc_body), (P // Tick ==> P') /\ (Q // Tick ==> Q') -> P ||| Q // Tick ==> P' ||| Q'
  (* Sequential Composition *)
  | seq_comp_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : event), (P // Event a ==> P') -> P ;; Q // Event a ==> P' ;; Q
  | seq_comp_tick_rule (P Q : proc_body) :
      forall (P' : proc_body), (P // Tick ==> P') -> P ;; Q // Tau ==> Q
  where "P '//' a '==>' Q" := (sosR P a Q).

Reserved Notation "P '///' t '==>' Q" (at level 150, left associativity).
Inductive sosStarR : proc_body -> list event_tau_tick -> proc_body -> Prop :=
  | sos_empty_rule (P : proc_body) :
      P /// nil ==> P
  | sos_transitive_rule (P R Q : proc_body) (head : event_tau_tick) (tail : list event_tau_tick) :
      (P // head ==> R) -> (R /// tail ==> Q) -> (P /// (head :: tail) ==> Q)
  where "P '///' t '==>' Q" := (sosStarR P t Q).
  
Definition traceBodyR (body : proc_body) (t : list event_tau_tick) :=
  exists (body' : proc_body), body /// t ==> body'.
  
Definition traceR (P : proc_def) (t : list event_tau_tick) :=
  match P with
  | Proc name body => traceBodyR body t
  end.

(** TRACE EXAMPLES **)

Definition PRINTER0 := "PRINTER0" ::= "accept" --> "print" --> STOP.

Example PRINTER0_empty_trace : traceR PRINTER0 nil.
Proof.
  unfold traceR. simpl.
  exists ("accept" --> "print" --> STOP).
  apply sos_empty_rule.
Qed.

Example PRINTER0_trace1 : traceR PRINTER0 [Event "accept"].
Proof.
  unfold traceR. simpl.
  exists ("print" --> STOP).
  apply sos_transitive_rule with (R := "print" --> STOP).
  - apply prefix_rule.
  - apply sos_empty_rule.
Qed.

Example PRINTER0_trace2 : traceR PRINTER0 [Event "accept" ; Event "print"].
Proof.
  unfold traceR. simpl.
  exists (STOP).
  apply sos_transitive_rule with (R := "print" --> STOP).
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := STOP).
    + apply prefix_rule.
    + apply sos_empty_rule.
Qed.

(* Note the following proof with eapply. In some sense, it's easier.
   However, in the end we get "remaining goals are on the shelf".
   
   To conclude the proof, I removed this goal from the shelf,
   and provided a trivial example of a proc_body.
   
   More information about "the shelf":
   - https://github.com/coq/coq/issues/8770
   - https://coq-club.inria.narkive.com/PQalG3f4/how-to-solve-trivial-evars-automatically-so-that-they-don-t-get-shelved
*)

Example PRINTER0_trace2' : traceR PRINTER0 [Event "accept" ; Event "print"].
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

Definition CHOOSE := "CHOOSE" ::= "select" --> ("keep" --> SKIP 
                                                [] "return" --> "CHOOSE").
Example CHOOSE_trace1 : traceR CHOOSE [Event "select" ; Event "keep"].
Proof.
  unfold traceR. simpl.
  exists (SKIP).
  apply sos_transitive_rule with (R := "keep" --> SKIP [] "return" --> "CHOOSE").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := SKIP).
    * apply ext_choice_left_rule.
      apply prefix_rule.
    * apply sos_empty_rule.
Qed.

Example CHOOSE_trace2 : traceR CHOOSE [Event "select" ; Event "return"].
Proof.
  unfold traceR. simpl.
  exists ("CHOOSE").
  apply sos_transitive_rule with (R := "keep" --> SKIP [] "return" --> "CHOOSE").
  - apply prefix_rule.
  - apply sos_transitive_rule with (R := "CHOOSE").
    * apply ext_choice_right_rule.
      apply prefix_rule.
    * apply sos_empty_rule.
Qed.

Definition PETE := "PETE" ::= "lift_piano" --> "PETE"
                              |~| "lift_table" --> "PETE".

Definition DAVE := "DAVE" ::= "lift_piano" --> "DAVE"
                              |~| "lift_table" --> "DAVE".

Definition TEAM := "TEAM" ::= "PETE" [| Alphabet {{"lift_piano", "lift_table"}} |] "DAVE".

(* TODO Revisit once the reference_rule is defined. *)
Example TEAM_trace1 : traceR TEAM [Event "lift_piano"].
Proof.
  unfold traceR. simpl.
  exists ("TEAM").
  apply sos_transitive_rule with (R := "PETE" [| Alphabet {{"lift_piano", "lift_table"}} |] "DAVE").
  - apply gener_parall_joint_rule. Abort.

Example LIGHT_trace1 : traceR ("LIGHT" ::= "on" --> "off" --> "LIGHT") [Event "on" ; Event "off" ; Event "on"].
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

Definition PUMP1 := "lift_nozzle_1" --> "READY1".
Definition READY1 := "replace_nozzle_1" --> "PUMP1"
                      [] "depress_trigger_1" --> "release_trigger_1" --> "READY1".
Definition PUMP2 := "lift_nozzle_2" --> "READY2".
Definition READY2 := "replace_nozzle_2" --> "PUMP2"
                      [] "depress_trigger_2" --> "release_trigger_2" --> "READY2".
Definition FORECOURT := "FORECOURT" ::= PUMP1 ||| PUMP2.

(* TODO Revisit once the reference_rule is defined. *)
Example FORECOURT_trace1 : traceR FORECOURT [Event "lift_nozzle_1" ; Event "depress_trigger_1" ; Event "lift_nozzle_2" ;
                                            Event "depress_trigger_2" ; Event "release_trigger_2"].
Proof.
  unfold traceR. simpl.
  exists("release_trigger_1" --> READY1 ||| READY2).
  apply sos_transitive_rule with (R := READY1 ||| PUMP2).
  - apply interleave_left_rule. unfold PUMP1. apply prefix_rule.
  - apply sos_transitive_rule with (R := "release_trigger_1" --> READY1 ||| PUMP2).
    * apply interleave_left_rule. apply ext_choice_right_rule. apply prefix_rule.
    * apply sos_transitive_rule with (R := "release_trigger_1" --> READY1 ||| READY2).
      + apply interleave_right_rule. unfold PUMP2. apply prefix_rule.
      + apply sos_transitive_rule with (R := "release_trigger_1" --> READY1 ||| "release_trigger_2" --> READY2).
        { apply interleave_right_rule. apply ext_choice_right_rule. apply prefix_rule. }
        { 
          apply sos_transitive_rule with (R := "release_trigger_1" --> READY1 ||| READY2).
          { apply interleave_right_rule. apply prefix_rule. }
          { apply sos_empty_rule. }
        }
Qed.
