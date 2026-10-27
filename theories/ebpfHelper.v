From Coq Require Import ZArith.
From compcert Require Import Integers Values Memory.
From bpf.semantics Require Import ebpfState.

Record helper_spec := {
  helper_pre: regset -> mem -> bool;
  helper_post: regset -> mem -> val -> mem -> bool
}.


Definition bpf_get_prandom_u32_spec: helper_spec := {|
  helper_pre := fun _ _ => true;
  helper_post := fun _ m result m' =>
    match result with
    | Vlong n => Z.ltb (Int64.unsigned n) (2 ^ 32)
    | _ => false
    end
|}.
