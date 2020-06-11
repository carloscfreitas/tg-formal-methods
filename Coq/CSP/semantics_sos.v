Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Require Import syntax.

Reserved Notation "S '#' P '//' a '==>' Q" (at level 150, left associativity).
Inductive sosR : specification -> proc_body -> event_tau_tick -> proc_body -> Prop :=
  (* Prefix *)
  | prefix_rule (S : specification) (P : proc_body) (a : event) :
      S # (a --> P) // Event a ==> P
  (* Reference *)
  (* This inference rule is different from the one implemented in the FDR tool. This approach will
    allow an ill-formed recursion such as P = P to be defined, by introducing a transition which communicates
    the internal event tau and, therefore, increasing the process LTS size. *)
  | reference_rule (S : specification) (P : proc_body) (name : string) :
      forall (Q : proc_body),
        eq P (ProcRef name) ->
        eq (get_proc_body S name) (Some Q) ->
        S # P // Tau ==> Q
  (* External Choice *)
  | ext_choice_left_rule (S : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
        ~ eq a Tau ->
        (S # P // a ==> P') ->
        (S # P [] Q // a ==> P')
  | ext_choice_right_rule (S : specification) (P Q : proc_body) :
      forall (Q' : proc_body) (a : event_tau_tick),
        ~ eq a Tau ->
        (S # Q // a ==> Q') ->
        (S # P [] Q // a ==> Q')
  | ext_choice_tau_left_rule (S : specification) (P Q : proc_body) :
      forall (P' : proc_body),
        (S # P // Tau ==> P') ->
        (S # P [] Q // Tau ==> P' [] Q)
  | ext_choice_tau_right_rule (S : specification) (P Q : proc_body) :
      forall (Q' : proc_body),
        (S # Q // Tau ==> Q') ->
        (S # P [] Q // Tau ==> P [] Q')
  (* Internal Choice *)
  | int_choice_left_rule (S : specification) (P Q : proc_body) :
      S # P |~| Q // Tau ==> P
  | int_choice_right_rule (S : specification) (P Q : proc_body) :
      S # P |~| Q // Tau ==> Q
  (* Alphabetised Parallel *)
  | alpha_parall_indep_left_rule (S : specification) (P Q : proc_body) (A B : set event) :
      forall (P' : proc_body) (a : event),
        set_In a (set_diff event_dec A B) ->
        (S # P // Event a ==> P') ->
        S # P [[ A \\ B ]] Q // Event a ==> P' [[ A \\ B ]] Q
  | alpha_parall_indep_right_rule (S : specification) (P Q : proc_body) (A B : set event) :
      forall (Q' : proc_body) (a : event),
        set_In a (set_diff event_dec B A) ->
        (S # Q // Event a ==> Q') ->
        S # P [[ A \\ B ]] Q // Event a ==> P [[ A \\ B ]] Q'
  | alpha_parall_tau_indep_left_rule (S : specification) (P Q : proc_body) (A B : set event) :
      forall (P' : proc_body),
        (S # P // Tau ==> P') ->
        S # P [[ A \\ B ]] Q // Tau ==> P' [[ A \\ B ]] Q
  | alpha_parall_tau_indep_right_rule (S : specification) (P Q : proc_body) (A B : set event) :
      forall (Q' : proc_body),
        (S # Q // Tau ==> Q') ->
        S # P [[ A \\ B ]] Q // Tau ==> P [[ A \\ B ]] Q'
  | alpha_parall_joint_rule (S : specification) (P Q : proc_body) (A B : set event) :
      forall (P' Q' : proc_body) (a : event),
        set_In a (set_inter event_dec A B) ->
        (S # P // Event a ==> P') ->
        (S # Q // Event a ==> Q') ->
        S # P [[ A \\ B ]] Q // Event a ==> P' [[ A \\ B ]] Q'
  | alpha_parall_tick_joint_rule (S : specification) (P Q : proc_body) (A B : set event) :
      forall (P' Q' : proc_body),
        (S # P // Tick ==> P') ->
        (S # Q // Tick ==> Q') ->
        S # P [[ A \\ B ]] Q // Tick ==> P' [[ A \\ B ]] Q'
  (* Generalised Parallel *)
  | gener_parall_indep_left_rule (S : specification) (P Q : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event),
        ~ set_In a A ->
        (S # P // Event a ==> P') ->
        S # P [| A |] Q // Event a ==> P' [| A |] Q
  | gener_parall_indep_right_rule (S : specification) (P Q : proc_body) (A : set event) :
      forall (Q' : proc_body) (a : event),
        ~ set_In a A ->
        (S # Q // Event a ==> Q') ->
        S # P [| A |] Q // Event a ==> P [| A |] Q'
  | gener_parall_tau_indep_left_rule (S : specification) (P Q : proc_body) (A : set event) :
      forall (P' : proc_body),
        (S # P // Tau ==> P') ->
        S # P [| A |] Q // Tau ==> P' [| A |] Q
  | gener_parall_tau_indep_right_rule (S : specification) (P Q : proc_body) (A : set event) :
      forall (Q' : proc_body),
        (S # Q // Tau ==> Q') ->
        S # P [| A |] Q // Tau ==> P [| A |] Q'
  | gener_parall_joint_rule (S : specification) (P Q : proc_body) (A : set event) :
      forall (P' Q' : proc_body) (a : event),
        set_In a A ->
        (S # P // Event a ==> P') ->
        (S # Q // Event a ==> Q') ->
        S # P [| A |] Q // Event a ==> P' [| A |] Q'
  | gener_parall_tick_joint_rule (S : specification) (P Q : proc_body) (A : set event) :
      forall (P' Q' : proc_body),
        (S # P // Tick ==> P') ->
        (S # Q // Tick ==> Q') ->
        S # P [| A |] Q // Tick ==> P' [| A |] Q'
  (* Interleave *)
  | interleave_left_rule (P Q : proc_body) :
      forall (S : specification) (P' : proc_body) (a : event_tau_tick),
        ~ eq a Tick ->
        (S # P // a ==> P') ->
        S # P ||| Q // a ==> P' ||| Q
  | interleave_right_rule (S : specification) (P Q : proc_body) :
      forall (Q' : proc_body) (a : event_tau_tick),
        ~ eq a Tick ->
        (S # Q // a ==> Q') ->
        S # P ||| Q // a ==> P ||| Q'
  | interleave_tick_rule (S : specification) (P Q : proc_body) :
      forall (P' Q' : proc_body),
        (S # P // Tick ==> P') ->
        (S # Q // Tick ==> Q') ->
        S # P ||| Q // Tick ==> P' ||| Q'
  (* Sequential Composition *)
  (* This inference rule is different from the one implemented in the FDR tool. The main consequence
    of this approach is that the transition resulting from the communication of the internal event tau
    will not be supressed and, therefore, will appear in the LTS. *)
  | seq_comp_rule (S : specification) (P Q : proc_body) :
      forall (P' : proc_body) (a : event_tau_tick),
        ~ eq a Tick ->
        (S # P // a ==> P') ->
        S # P ;; Q // a ==> P' ;; Q
  | seq_comp_tick_rule (S : specification) (P Q : proc_body) :
      forall (P' : proc_body),
        (S # P // Tick ==> P') ->
        S # P ;; Q // Tau ==> Q
  (* Hiding *)
  | hiding_rule (S : specification) (P : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event),
        set_In a A ->
        (S # P // Event a ==> P') ->
        S # P \ A // Tau ==> P' \ A
  | hiding_not_hidden_rule (S : specification) (P : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event),
        ~ set_In a A ->
        (S # P // Event a ==> P') ->
        S # P \ A // Event a ==> P' \ A
  | hiding_tau_tick_rule (S : specification) (P : proc_body) (A : set event) :
      forall (P' : proc_body) (a : event_tau_tick),
        (eq a Tau \/ eq a Tick) ->
        (S # P // a ==> P') ->
        S # P \ A // a ==> P' \ A
  (* Successful Termination - Schneider, p. 11 (PDF: 29) *)
  | success_termination_rule (S : specification) :
      S # SKIP // Tick ==> STOP
  where "S '#' P '//' a '==>' Q" := (sosR S P a Q).

Reserved Notation "S '#' P '///' t '==>' Q" (at level 150, left associativity).
Inductive sosStarR : specification -> proc_body -> list event_tau_tick -> proc_body -> Prop :=
  | sos_empty_rule (S : specification) (P : proc_body) :
      S # P /// nil ==> P
  | sos_transitive_rule (S : specification) (P R Q : proc_body) (head : event_tau_tick) (tail : list event_tau_tick) :
      (S # P // head ==> R) -> (S # R /// tail ==> Q) -> (S # P /// (head :: tail) ==> Q)
  where "S '#' P '///' t '==>' Q" := (sosStarR S P t Q).