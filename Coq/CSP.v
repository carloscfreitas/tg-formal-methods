Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Open Scope string_scope.

(** TYPE DEFINITIONS **)

(* TODO Check if the "event" type could be defined as a notation
  instead of a inductive type. *)

Notation event := string.

(* Inductive event : Type :=
  | Event (name : string). *)

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

Fixpoint proc_eqb (P Q : proc_body) : Prop :=
  match P, Q with
  | SKIP, SKIP => True
  | STOP, STOP => True
  | ProcRef a, ProcRef b => eq a b
  | ProcPrefix a A, ProcPrefix b B => eq a b /\ proc_eqb A B
  (* | ProcExtChoice A B, ProcExtChoice X Y => proc_eqb A B /\ proc_eqb X Y
  | ProcIntChoice A B, ProcIntChoice X Y => proc_eqb A B /\ proc_eqb X Y
  | ProcAlphaParallel A B K L, ProcAlphaParallel X Y M N => proc_eqb A B /\ proc_eqb X Y /\ eq K M /\ eq L N
  | ProcGenParallel A B K, ProcGenParallel X Y M => proc_eqb A B /\ proc_eqb X Y /\ eq K M
  | ProcInterleave A B, ProcInterleave X Y => proc_eqb A B /\ proc_eqb X Y
  | ProcSeqComp A B, ProcSeqComp X Y => proc_eqb A B /\ proc_eqb X Y *)
  | _, _ => False
end.

(** NOTATIONS/COERCIONS **)

(* TODO Prove that equality is decidable for event type. *)
Check string_dec.
Definition event_dec := string_dec.

(* Notations for declaring sets of events. *)
Notation "{ }" := (empty_set event) (format "{ }").
Notation "{ x }" := (set_add event_dec x (empty_set event)). (* TODO This notation is not working properly. *)
Notation "{ x , y , .. , z }" := (set_add event_dec x (set_add event_dec y .. (set_add event_dec z (empty_set event)) ..)).

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
(* Alphabetised Parallel (TODO This notation is not working properly.) *)
Notation "P [ A || B ] Q" := (ProcAlphaParallel P Q A B) (at level 90, no associativity).
(* Generalised (or Interface) Parallel *)
Notation "P [| A |] Q" := (ProcGenParallel P Q A) (at level 90, no associativity).
(* Interleaving *)
Notation "P ||| Q" := (ProcInterleave P Q) (at level 90, left associativity).
(* Sequencial Composition (";" is already defined in list notations) *)
Notation "P ;; Q" := (ProcSeqComp P Q) (at level 90, left associativity).

(* Example 3.20 (book) using notations. *)
Definition SPurchase := 
  (
    Spec
    [
      Channel {"select", "keep", "return"}
      ; Channel {"cash", "cheque", "card"}
      ; Channel {"swipe", "sign"}
      ; Channel {"receipt", "reject"}
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

(* TODO: here, "string" is an event in the semantic level, with tick and tau *)

(* TODO: I would prefer proc_body -> event -> proc_body, but this
         change has an impact in the notation definition before *)

(* TODO Constraint the event sets in the transition rules bellow according to the book.
  (i.e. whether to include tick and tau events in the alphabet)  *)
Reserved Notation "P '//' a '==>' Q" (at level 150, left associativity).
Inductive sosR : proc_body -> string -> proc_body -> Prop :=
  (* Prefix *)
  | prefix_rule (P Q : proc_body) (a : string) :
      (a --> P) // a ==> Q
  (* Recursion *)
  | recursion_rule (P : proc_body) :
      forall (P' N : proc_body) (a : string), (P // a ==> P') /\ (proc_eqb P N) -> N // a ==> P'
  (* External Choice *)
  | ext_choice_left_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> (P [] Q // a ==> P')
  | ext_choice_right_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> (Q [] P // a ==> P')
  (* Internal Choice *)
  | int_choice_left_rule (P Q : proc_body) :
      forall (tau : string), P |~| Q // tau ==> P
  | int_choice_right_rule (P Q : proc_body) (tau : string) :
      forall (tau : string), P |~| Q // tau ==> Q
  (* Alphabetised Parallel *)
  | alpha_parall_indep_left_rule (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> (ProcAlphaParallel P Q A B) // a ==> (ProcAlphaParallel P' Q A B)
  | alpha_parall_indep_right_rule (P Q : proc_body) (A B : alphabet) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> (ProcAlphaParallel Q P A B) // a ==> (ProcAlphaParallel Q P' A B)
  | alpha_parall_joint_rule (P Q : proc_body) (A B : alphabet) :
      forall (P' Q' : proc_body) (a : string), (P // a ==> P') -> (Q // a ==> Q') -> (ProcAlphaParallel P Q A B) // a ==> (ProcAlphaParallel P' Q' A B)
  (* Generalised Parallel *)
  | gener_parall_indep_left_rule (P Q : proc_body) (A : alphabet) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> P [| A |] Q // a ==> P' [| A |] Q
  | gener_parall_indep_right_rule (P Q : proc_body) (A : alphabet) :
    forall (P' : proc_body) (a : string), (P // a ==> P') -> Q [| A |] P // a ==> Q [| A |] P'
  | gener_parall_joint_rule (P Q : proc_body) (A : alphabet) :
      forall (P' Q' : proc_body) (a : string), (P // a ==> P') -> (Q // a ==> Q') -> P [| A |] Q // a ==> P' [| A |] Q'
  (* Interleave *)
  | interleave_left_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> P ||| Q // a ==> P' ||| Q
  | interleave_right_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> Q ||| P // a ==> Q ||| P'
  | interleave_tick_rule (P Q : proc_body) :
      (* TODO Check if there is indeed a conjuction in this transition rule. *)
      forall (P' Q' : proc_body) (tick : string), (P // tick ==> P') /\ (Q // tick ==> Q') -> P ||| Q // tick ==> P' ||| Q'
  (* Sequential Composition *)
  | seq_comp_rule (P Q : proc_body) :
      forall (P' : proc_body) (a : string), (P // a ==> P') -> P ;; Q // a ==> P' ;; Q
  | seq_comp_tick_rule (P Q : proc_body) :
      forall (P' : proc_body) (tick tau : string), (P // tick ==> P') -> P ;; Q // tau ==> Q
  where "P '//' a '==>' Q" := (sosR P a Q).

Reserved Notation "P '///' t '==>' Q" (at level 150, left associativity).
Inductive sosStarR : proc_body -> list string -> proc_body -> Prop :=
  | sos_empty_rule (P : proc_body) :
      P /// nil ==> P
  | sos_transitive_rule (P R Q : proc_body) (head : string) (tail : list string) :
      (P // head ==> R) -> (R /// tail ==> Q) -> (P /// (head :: tail) ==> Q)
  where "P '///' t '==>' Q" := (sosStarR P t Q).
  
Definition traceBodyR (body : proc_body) (t : list string) :=
  exists (body' : proc_body), body /// t ==> body'.
  
Definition traceR (P : proc_def) (t : list string) :=
  match P with
  | Proc name body => traceBodyR body t
  end.

Definition PRINTER0 := "PRINTER0" ::= "accept" --> "print" --> STOP.

Example PRINTER0_empty_trace : traceR PRINTER0 nil.
Proof.
  unfold traceR. simpl.
  exists ("accept" --> "print" --> STOP).
  apply sos_empty_rule.
Qed.

Example PRINTER0_trace1 : traceR PRINTER0 ["accept"].
Proof.
  unfold traceR. simpl.
  exists ("print" --> STOP).
  apply sos_transitive_rule with (R := "print" --> STOP).
  - apply prefix_rule.
  - apply sos_empty_rule.
Qed.

Example PRINTER0_trace2 : traceR PRINTER0 ["accept" ; "print"].
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

Example PRINTER0_trace2' : traceR PRINTER0 ["accept" ; "print"].
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
Example CHOOSE_trace1 : traceR CHOOSE ["select" ; "keep"].
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

Example CHOOSE_trace2 : traceR CHOOSE ["select" ; "return"].
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

Definition TEAM := "TEAM" ::= "PETE" [| Alphabet {"lift_piano", "lift_table"} |] "DAVE".

Example TEAM_trace1 : traceR TEAM ["lift_piano"].
Proof.
  unfold traceR. simpl.
  exists ("TEAM").
  apply sos_transitive_rule with (R := "PETE" [| Alphabet {"lift_piano", "lift_table"} |] "DAVE").
  - apply gener_parall_joint_rule.
    * apply recursion_rule with (P := "lift_piano" --> "PETE" |~| "lift_table" --> "PETE"). split.
      + Fail eapply int_choice_left_rule. Abort.

Example LIGHT_trace1 : traceR ("LIGHT" ::= "on" --> "off" --> "LIGHT") ["on" ; "off" ; "on"].
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
