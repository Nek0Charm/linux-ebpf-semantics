From Coq Require Import List.

(** Abstract syntax and semantics for RISC-V assembly language. *)

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.  (*
From compcert.common Require Import Globalenvs. *) (*
From compcert Require Import Locations. *)

From compcert Require Import Conventions Events Smallstep.
From compcert Require Stacklayout.
From compcert Require Import Op.

From bpf.ebpf Require Import GlobalSem ebpfSyntax.

Import ListNotations.

(*
Definition dummy_function := mkfunction signature_main 0 nil. *)

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

Definition regset := Pregmap.t val. (*
Definition genv := Genv.t fundef unit. *)

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.
Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.


(*
Variable ge: genv. *)


Record cstk' := mk_cstk' {
  stk_ra: val;
  stk_r6: val;
  stk_r7: val;
  stk_r8: val;
  stk_r9: val;
  stk_r10: val;
}.

Definition cstk := list cstk'.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)
  
Inductive outcome : Type :=
  | Next: regset -> cstk -> option nat -> nat -> mem -> outcome
  | Stuck: outcome.


Record addr_region := {
  base_blk: block;
  size_blk: Z;
  base_addr: int64;
}.