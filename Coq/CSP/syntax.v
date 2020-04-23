Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

(** TYPE DEFINITIONS **)

Definition event := string.
Definition event_dec := string_dec.

Inductive event_tau_tick :=
  | Event (e : event)
  | Tau
  | Tick.

Theorem event_tau_tick_eq_dec :
  forall (e1 e2 : event_tau_tick),
    {e1 = e2} + {e1 <> e2}.
Proof.
  intros. destruct e1, e2 ; try (left ; reflexivity) ;
  try (right ; unfold not ; intros H ; now inversion H).
  decide equality. apply event_dec.
Defined.

Inductive alphabet : Type :=
  | Alphabet (events : set event).
  
Theorem alphabet_eq_dec :
  forall (a1 a2 : alphabet),
    {a1 = a2} + {a1 <> a2}.
Proof.
  intros. destruct a1, a2.
  repeat (decide equality ; try apply event_dec).
Defined.

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
  | ProcSeqComp (proc1 proc2 : proc_body)
  | ProcHiding (proc: proc_body) (alph : alphabet).

Theorem proc_body_eq_dec :
  forall (p1 p2 : proc_body),
    {p1 = p2} + {p1 <> p2}.
Proof.
  intros. destruct p1, p2 ;
    try (right ; unfold not ; intros H ; now inversion H) ;
    try (left ; reflexivity) ;
    decide equality ; try apply event_dec ; try apply alphabet_eq_dec.
Defined.

Inductive proc_def : Type :=
  | Proc (name : string) (body : proc_body).

Inductive specification : Type :=
  | Spec (ch_list : list channel) (proc_list : list proc_def).

Fixpoint find_proc_body (proc_list : list proc_def) (proc_name : string) : option proc_body :=
  match proc_list with
  | [] => None
  | (Proc name body) :: tail => match eqb proc_name name with
                                | true => Some body
                                | false => find_proc_body tail proc_name
                                end
  end.

Definition get_proc_body (context : specification) (proc_name : string) : option proc_body :=
  match context with
  | Spec ch_list proc_list => find_proc_body proc_list proc_name
  end.

(** NOTATIONS/COERCIONS **) 

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
Notation "P [[ A \\ B ]] Q" := (ProcAlphaParallel P Q (Alphabet A) (Alphabet B)) (at level 90, no associativity).
(* Generalised (or Interface) Parallel *)
Notation "P [| A |] Q" := (ProcGenParallel P Q (Alphabet A)) (at level 90, no associativity).
(* Interleaving *)
Notation "P ||| Q" := (ProcInterleave P Q) (at level 90, left associativity).
(* Sequencial Composition *)
Notation "P ;; Q" := (ProcSeqComp P Q) (at level 90, left associativity).
(* Hiding *)
Notation "P \ A" := (ProcHiding P (Alphabet A)) (at level 96, left associativity).