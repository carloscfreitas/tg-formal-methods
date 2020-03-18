From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

(** TYPE DEFINITIONS **)

(* TODO Remove ETick and ETau.*)
Inductive event : Type :=
  | Event (name : string)
  | ETick
  | ETau.

(* TODO Use ListSet and define notations. *)
Inductive alphabet : Type :=
  | Alphabet (events : list event).

Inductive channel : Type :=
  | Channel (events : list event).

Compute (Channel [Event "print" ; Event "accept"]).

(* TODO Rename ProcName to ProcRef. *)
Inductive proc_body : Type :=
  | SKIP
  | STOP
  | ProcName (name : string) (* A reference to a process, including itself (recursion). *)
  | ProcPrefix (event : event) (proc : proc_body)
  | ProcExtChoice (proc1 proc2 : proc_body)
  | ProcIntChoice (proc1 proc2 : proc_body)
  | ProcAlphaParallel (proc1 proc2 : proc_body) (alph1 alph2 : alphabet)
  | ProcGenParallel (proc1 proc2 : proc_body) (alph : alphabet)
  | ProcInterleave (proc1 proc2 : proc_body)
  | ProcSeqComp (proc1 proc2 : proc_body).

Inductive proc_def : Type :=
  | Proc (name : string) (body : proc_body).

(* TODO Define especification as a list of channels and processes. *)

(* Example 1.6 (book): PRINTER0 = accept -> print -> STOP *)
Compute (Proc "PRINTER0" (ProcPrefix (Event "accept") (ProcPrefix (Event "print") STOP))).

(* Example 1.14 (book): LIGHT = on -> off -> LIGHT *)
Compute Proc "LIGHT" (ProcPrefix (Event "on") (ProcPrefix (Event "off") (ProcName "LIGHT"))).

(** NOTATIONS **)

(* TODO Try to use coercion instead of notation for this constructor. *)
Notation "@ Q" := (ProcName Q) (at level 100, no associativity).
(* Process definition. TODO use "::=" instead. *)
Notation "P == Q" := (Proc P Q) (at level 100).
(* Prefix *)
Notation "a --> P" := (ProcPrefix (Event a) P) (at level 80, right associativity).
(* External Choice *)
Notation "P [] Q" := (ProcExtChoice P Q) (at level 90, left associativity).
(* Internal Choice *)
Notation "P |~| Q" := (ProcIntChoice P Q) (at level 90, left associativity).
(* Alphabetised Parallel *)
Notation "P [ A || B ] Q" := (ProcAlphaParallel P Q A B) (at level 90, no associativity).
(* Generalised (or Interface) Parallel *)
Notation "P [| A |] Q" := (ProcGenParallel P Q A) (at level 90, no associativity).
(* Interleaving *)
Notation "P ||| Q" := (ProcInterleave P Q) (at level 90, left associativity).
(* Sequencial Composition *)
Notation "P ; Q" := (ProcSeqComp P Q) (at level 90, left associativity).

Unset Printing Notations.

(* Example 1.6 (book) but with notations. *)
Compute "PRINTER0" == "accept" --> "print" --> STOP.

(* Example 1.14 (book) but with notations. *)
Compute "LIGHT" == "on" --> "off" --> (@ "LIGHT").

(* Example 3.20 (book) using notations. *)
Definition PChoose := "CHOOSE" == "select" --> ("keep" --> SKIP 
                                                [] "return" --> (@ "CHOOSE")).
Definition PPay := "PAY" == "cash" --> "receipt" --> SKIP
                            [] "cheque" --> "receipt" --> SKIP
                            [] "card" --> "swipe" --> ("sign" --> "receipt" --> SKIP
                                                       [] "reject" --> (@ "PAY")).
Definition PPurchase := "PURCHASE" == (@ "CHOOSE") ; (@ "PAY").
Print PPurchase.

(* TODO: here, "string" is an event in the semantic level, with tick and tau *)

(* TODO: I would prefer proc_body -> event -> proc_body, but this
         change has an impact in the notation definition before *)

Reserved Notation "P '//' a '==>' Q" (at level 150, left associativity).
Inductive sosR : proc_body -> string -> proc_body -> Prop :=
  | prefix_rule (P Q : proc_body) (a : string) :
      (a --> P) // a ==> Q
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

Definition PRINTER0 := "PRINTER0" == "accept" --> "print" --> STOP.

Local Open Scope string.
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

(* TODO: for some reason, writing ["accept" ; "print"] raises an error
         I have the impression that it is related to your notation *)

Example PRINTER0_trace2 : traceR PRINTER0 ("accept" :: ["print"]).
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

Example PRINTER0_trace2' : traceR PRINTER0 ("accept" :: ["print"]).
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
Local Close Scope string.