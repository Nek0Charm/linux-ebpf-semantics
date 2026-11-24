From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory.
From bpf.semantics Require Import ebpfState.

Import ListNotations.
Open Scope Z_scope.

Inductive helper_postcondition :=
  | NoMemoryEffect (returns: val -> bool)
  | MemoryPost (holds: regset -> mem -> val -> mem -> bool).

Record helper_spec := {
  helper_id: Z;
  (* None denotes an unconditional precondition. *)
  helper_pre: option (regset -> mem -> bool);
  helper_post: helper_postcondition
}.

Definition helper_pre_holds (spec: helper_spec) (rs: regset) (m: mem) : bool :=
  match helper_pre spec with
  | None => true
  | Some pre => pre rs m
  end.

Definition helper_post_holds (spec: helper_spec) (rs: regset)
    (m: mem) (result: val) (m': mem) : Prop :=
  match helper_post spec with
  | NoMemoryEffect returns => returns result = true /\ m' = m
  | MemoryPost holds => holds rs m result m' = true
  end.

Definition bpf_get_prandom_u32: helper_spec := {|
  helper_id := 7;
  helper_pre := None;
  helper_post := NoMemoryEffect (fun result =>
    match result with
    | Vlong n => Z.ltb (Int64.unsigned n) (2 ^ 32)
    | _ => false
    end)
|}.

Definition find_helper (id: Z): option helper_spec :=
  List.find (fun spec => Z.eqb id (helper_id spec)) [bpf_get_prandom_u32].
