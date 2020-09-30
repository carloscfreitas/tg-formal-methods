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
    [ Channel {{"coat_off", "coat_on", "request_coat", "retrieve", "store", "eat"}} ]
    [ "SYSTEM" ::=
      "coat_off" --> "store" --> "request_coat" --> "retrieve" --> "coat_on" --> SKIP
      [| {{"coat_off", "request_coat", "coat_on"}} |]
      "coat_off" --> "eat" --> "request_coat" --> "coat_on" --> SKIP ]
  ).
Defined.

Compute generate_dot (compute_ltsR example "SYSTEM" 100).

Local Close Scope string.