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

Definition event_tau_tick_to_str (e : event_tau_tick) : string :=
  match e with
  | Tau => "τ"
  | Tick => "✓"
  | Event a => a
  end.

Coercion event_tau_tick_to_str : event_tau_tick >-> string.

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

Definition get_proc_id (p : proc_def) : string :=
  match p with
  | Proc id body => id
  end.

Fixpoint concat_channels (ch_list : list channel) : list event :=
  match ch_list with
  | (Channel ch) :: tl => ch ++ concat_channels tl
  | nil => nil
  end.

Fixpoint get_proc_refs' (P : proc_body) : set string :=
  match P with
  | SKIP => empty_set string
  | STOP => empty_set string
  | ProcRef id => set_add string_dec id (empty_set string)
  | ProcPrefix _ P' => get_proc_refs' P'
  | ProcExtChoice P' P'' => set_union string_dec (get_proc_refs' P') (get_proc_refs' P'')
  | ProcIntChoice P' P'' => set_union string_dec (get_proc_refs' P') (get_proc_refs' P'')
  | ProcAlphaParallel P' P'' _ _ => set_union string_dec (get_proc_refs' P') (get_proc_refs' P'')
  | ProcGenParallel P' P'' _ => set_union string_dec (get_proc_refs' P') (get_proc_refs' P'')
  | ProcInterleave P' P'' => set_union string_dec (get_proc_refs' P') (get_proc_refs' P'')
  | ProcSeqComp P' P'' => set_union string_dec (get_proc_refs' P') (get_proc_refs' P'')
  | ProcHiding P' _ => get_proc_refs' P'
  end.

Fixpoint get_proc_refs (proc_def_list : list proc_def) : set string :=
  match proc_def_list with
  | (Proc id body) :: tail => set_union string_dec (get_proc_refs' body) (get_proc_refs tail)
  | nil => nil
  end.

Fixpoint get_events' (P : proc_body) : set event :=
  match P with
  | SKIP => empty_set event
  | STOP => empty_set event
  | ProcRef id => empty_set event
  | ProcPrefix e P' => set_add event_dec e (get_events' P')
  | ProcExtChoice P' P'' => set_union event_dec (get_events' P') (get_events' P'')
  | ProcIntChoice P' P'' => set_union event_dec (get_events' P') (get_events' P'')
  | ProcAlphaParallel P' P'' (Alphabet A) (Alphabet B) =>
    set_union event_dec A (set_union event_dec B (set_union event_dec (get_events' P') (get_events' P'')))
  | ProcGenParallel P' P'' (Alphabet A) =>
    set_union event_dec A (set_union event_dec (get_events' P') (get_events' P''))
  | ProcInterleave P' P'' => set_union event_dec (get_events' P') (get_events' P'')
  | ProcSeqComp P' P'' => set_union event_dec (get_events' P') (get_events' P'')
  | ProcHiding P' (Alphabet A) => set_union event_dec A (get_events' P')
  end.

Fixpoint get_events (proc_def_list : list proc_def) : set string :=
  match proc_def_list with
  | (Proc id body) :: tail => set_union string_dec (get_events' body) (get_events tail)
  | nil => nil
  end.

Record specification : Type := Build_Spec
{
  ch_list : list channel;
  proc_list : list proc_def;
  non_empty_proc_ids : ~ In EmptyString (map get_proc_id proc_list);
  non_empty_events : ~ In EmptyString (concat_channels ch_list);
  no_dup_proc_ids : NoDup (map get_proc_id proc_list);
  no_dup_events : NoDup (concat_channels ch_list);
  no_missing_proc_defs : incl (get_proc_refs proc_list) (map get_proc_id proc_list);
  no_missing_events : incl (get_events proc_list) (concat_channels ch_list)
}.

Fixpoint find_proc_body (proc_list : list proc_def) (proc_name : string) : option proc_body :=
  match proc_list with
  | [] => None
  | (Proc name body) :: tail => match eqb proc_name name with
                                | true => Some body
                                | false => find_proc_body tail proc_name
                                end
  end.

Definition get_proc_body (spec : specification) (proc_name : string) : option proc_body :=
  find_proc_body spec.(proc_list) proc_name.

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
(* TODO I had to comment this coercion because I was unable to pattern match the ProcRef
  constructor inside the tactic macro "solve_trace" (semantics_trace.v). *)
(* Definition str_to_proc_body (s : string) : proc_body := ProcRef s.
Coercion str_to_proc_body : string >-> proc_body. *)
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

Fixpoint proc_body_to_str (proc : proc_body) : string :=
  match proc with
  | SKIP => "SKIP"
  | STOP => "STOP"
  | ProcRef name => name
  | e --> P => e ++ " → " ++ proc_body_to_str P
  | P [] Q => proc_body_to_str P ++ " [] " ++ proc_body_to_str Q
  | P |~| Q => proc_body_to_str P ++ " |~| " ++ proc_body_to_str Q
  | P [[ A \\ B ]] Q => proc_body_to_str P ++ " [{" ++ (concat ", " A) ++ "} || {"
    ++ (concat ", " B) ++ "}] " ++ proc_body_to_str Q
  | P [| A |] Q => proc_body_to_str P ++ " [| {" ++ (concat ", " A) ++ "} |] " ++ proc_body_to_str Q
  | P ||| Q => proc_body_to_str P ++ " ||| " ++ proc_body_to_str Q
  | P ;; Q => proc_body_to_str P ++ "; " ++ proc_body_to_str Q
  | P \ A => proc_body_to_str P ++ " \\ " ++ "{" ++ (concat ", " A) ++ "}"
  end.

Coercion proc_body_to_str : proc_body >-> string.

Local Open Scope string_scope.

Ltac solve_not_in := unfold not;
  let H := fresh "H" in (
    intros H; repeat (contradiction + (destruct H; [> inversion H | ]))
  ).

Ltac solve_nodup := repeat (apply NoDup_cons; [> solve_not_in | ]); apply NoDup_nil.

Ltac solve_incl := unfold incl;
  let H := fresh "H" in (
    let a := fresh "a" in (
      intros a H;
      repeat (contradiction + (destruct H; [> repeat (repeat (right + left)); apply H | ]))
    )).

Ltac solve_spec_ctx_rules spec_cons := apply spec_cons;
  repeat (
    match goal with
    | |- ~ In _ _ => solve_not_in
    | |- NoDup _ => solve_nodup
    | |- incl _ _ => solve_incl
    end
  ); fail "One or more contextual rules were not fulfilled".

Definition S_FORECOURT : specification.
Proof.
  solve_spec_ctx_rules
  (
    Build_Spec
    [
      Channel {{"lift_nozzle_1", "lift_nozzle_1", "replace_nozzle_1", "depress_trigger_1", "release_trigger_1"}}
      ; Channel ["foo_bar" ; "lift_nozzle_2" ; "replace_nozzle_2" ; "depress_trigger_2" ; "release_trigger_2"]
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
Defined.

Local Close Scope string_scope.