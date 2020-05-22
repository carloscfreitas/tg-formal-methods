Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.

Reserved Notation "C '#' P '//' a '==>' Q" (at level 150, left associativity).
Inductive sosR : specification -> proc_body -> event_tau_tick -> proc_body -> Prop :=
  (* Prefix *)
  | prefix_rule (C : specification) (P : proc_body) (a : event) :
      C # (a --> P) // Event a ==> P
  (* Reference *)
  (* This inference rule is different from the one implemented in the FDR tool. This approach will
    allow an ill-formed recursion such as P = P to be defined, by introducing a transition which communicates
    the internal event tau and, therefore, increasing the process LTS size. *)
  | reference_rule (C : specification) (P : proc_body) (name : string) :
      forall (Q : proc_body),
        eq P (ProcRef name) ->
        eq (get_proc_body C name) (Some Q) ->
        C # P // Tau ==> Q
  (* External Choice *)
  | ext_choice_left_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
        ~ eq a Tau ->
        (C # P // a ==> P') ->
        (C # P [] Q // a ==> P')
  | ext_choice_right_rule (C : specification) (P Q : proc_body) :
      forall (Q' : proc_body) (a : event_tau_tick),
        ~ eq a Tau ->
        (C # Q // a ==> Q') ->
        (C # P [] Q // a ==> Q')
  | ext_choice_tau_left_rule (C : specification) (P Q : proc_body) :
      forall (P' : proc_body),
        (C # P // Tau ==> P') ->
        (C # P [] Q // Tau ==> P' [] Q)
  | ext_choice_tau_right_rule (C : specification) (P Q : proc_body) :
      forall (Q' : proc_body),
        (C # Q // Tau ==> Q') ->
        (C # P [] Q // Tau ==> P [] Q')
  (* Internal Choice *)
  | int_choice_left_rule (C : specification) (P Q : proc_body) :
      C # P |~| Q // Tau ==> P
  | int_choice_right_rule (C : specification) (P Q : proc_body) :
      C # P |~| Q // Tau ==> Q
  (* Alphabetised Parallel *)
  | alpha_parall_indep_left_rule (C : specification) (P Q : proc_body) (A B : set event) :
      forall (P' : proc_body) (a : event),
        set_In a (set_diff event_dec A B) ->
        (C # P // Event a ==> P') ->
        C # P [[ A \\ B ]] Q // Event a ==> P' [[ A \\ B ]] Q
  | alpha_parall_indep_right_rule (C : specification) (P Q : proc_body) (A B : set event) :
      forall (Q' : proc_body) (a : event),
        set_In a (set_diff event_dec B A) ->
        (C # Q // Event a ==> Q') ->
        C # P [[ A \\ B ]] Q // Event a ==> P [[ A \\ B ]] Q'
  | alpha_parall_tau_indep_left_rule (C : specification) (P Q : proc_body) (A B : set event) :
      forall (P' : proc_body),
        (C # P // Tau ==> P') ->
        C # P [[ A \\ B ]] Q // Tau ==> P' [[ A \\ B ]] Q
  | alpha_parall_tau_indep_right_rule (C : specification) (P Q : proc_body) (A B : set event) :
      forall (Q' : proc_body),
        (C # Q // Tau ==> Q') ->
        C # P [[ A \\ B ]] Q // Tau ==> P [[ A \\ B ]] Q'
  | alpha_parall_joint_rule (C : specification) (P Q : proc_body) (A B : set event) :
      forall (P' Q' : proc_body) (a : event),
        set_In a (set_inter event_dec A B) ->
        (C # P // Event a ==> P') ->
        (C # Q // Event a ==> Q') ->
        C # P [[ A \\ B ]] Q // Event a ==> P' [[ A \\ B ]] Q'
  | alpha_parall_tick_joint_rule (C : specification) (P Q : proc_body) (A B : set event) :
      forall (P' Q' : proc_body),
        (C # P // Tick ==> P') ->
        (C # Q // Tick ==> Q') ->
        C # P [[ A \\ B ]] Q // Tick ==> P' [[ A \\ B ]] Q'
  (* Generalised Parallel *)
  | gener_parall_indep_left_rule (C : specification) (P Q : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event),
        ~ set_In a A ->
        (C # P // Event a ==> P') ->
        C # P [| A |] Q // Event a ==> P' [| A |] Q
  | gener_parall_indep_right_rule (C : specification) (P Q : proc_body) (A : set event) :
      forall (Q' : proc_body) (a : event),
        ~ set_In a A ->
        (C # Q // Event a ==> Q') ->
        C # P [| A |] Q // Event a ==> P [| A |] Q'
  | gener_parall_tau_indep_left_rule (C : specification) (P Q : proc_body) (A : set event) :
      forall (P' : proc_body),
        (C # P // Tau ==> P') ->
        C # P [| A |] Q // Tau ==> P' [| A |] Q
  | gener_parall_tau_indep_right_rule (C : specification) (P Q : proc_body) (A : set event) :
      forall (Q' : proc_body),
        (C # Q // Tau ==> Q') ->
        C # P [| A |] Q // Tau ==> P [| A |] Q'
  | gener_parall_joint_rule (C : specification) (P Q : proc_body) (A : set event) :
      forall (P' Q' : proc_body) (a : event),
        set_In a A ->
        (C # P // Event a ==> P') ->
        (C # Q // Event a ==> Q') ->
        C # P [| A |] Q // Event a ==> P' [| A |] Q'
  | gener_parall_tick_joint_rule (C : specification) (P Q : proc_body) (A : set event) :
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
      forall (Q' : proc_body) (a : event_tau_tick),
        ~ eq a Tick ->
        (C # Q // a ==> Q') ->
        C # P ||| Q // a ==> P ||| Q'
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
  (* Hiding *)
  | hiding_rule (C : specification) (P : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event),
        set_In a A ->
        (C # P // Event a ==> P') ->
        C # P \ A // Tau ==> P' \ A
  | hiding_not_hidden_rule (C : specification) (P : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event),
        ~ set_In a A ->
        (C # P // Event a ==> P') ->
        C # P \ A // Event a ==> P' \ A
  | hiding_tau_tick_rule (C : specification) (P : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event_tau_tick),
        (eq a Tau \/ eq a Tick) ->
        (C # P // a ==> P') ->
        C # P \ A // a ==> P' \ A
  (* Successful Termination - Schneider, p. 11 (PDF: 29) *)
  | success_termination_rule (C : specification) :
      C # SKIP // Tick ==> STOP
  where "C '#' P '//' a '==>' Q" := (sosR C P a Q).

Reserved Notation "C '#' P '///' t '==>' Q" (at level 150, left associativity).
Inductive sosStarR : specification -> proc_body -> list event_tau_tick -> proc_body -> Prop :=
  | sos_empty_rule (C : specification) (P : proc_body) :
      C # P /// nil ==> P
  | sos_transitive_rule (C : specification) (P R Q : proc_body) (head : event_tau_tick) (tail : list event_tau_tick) :
      (C # P // head ==> R) -> (C # R /// tail ==> Q) -> (C # P /// (head :: tail) ==> Q)
  where "C '#' P '///' t '==>' Q" := (sosStarR C P t Q).