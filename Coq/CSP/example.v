Require Import CSP.lts.
Require Import CSP.semantics_sos.
Require Import CSP.semantics_trace.
Require Import CSP.syntax.
Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Strings.String.
Import ListNotations.

Local Open Scope string.

Definition example : specification.
Proof.
  solve_spec_ctx_rules (
    Build_Spec
    [
      Channel {{"start", "ev1", "ev2", "ev3", "end"}}
    ]
    [
      "P" ::= "start" --> ("ev1" --> SKIP [] "ev2" --> SKIP) ;; "end" --> ProcRef "P"
      ; "Q" ::= "start" --> "ev3" --> "end" --> ProcRef "Q"
      ; "R" ::= ProcRef "P" [| {{"start", "end"}} |] ProcRef "Q"
    ]
  ).
Defined.

Compute generate_dot (compute_ltsR example "R" 100).