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