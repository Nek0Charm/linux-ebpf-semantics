From Coq Require Import List.

(** Abstract syntax and semantics for RISC-V assembly language. *)

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.  (*
From compcert.common Require Import Globalenvs. *) (*
From compcert Require Import Locations. *)


Import ListNotations.



(** * Abstract syntax *)

(** Registers. *)

(** RFC9559: TODO *)
Inductive ireg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 
  | R10 (**r eBPF stack frame pointer *)
  | RAX (**r hidden auxiliary/helper register *).

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition ireg_eqb (x y: ireg) : bool :=
  if ireg_eq x y then true else false.

Definition caller_saved_registers: list ireg := [R1; R2; R3; R4; R5].
Definition callee_saved_registers: list ireg := [R6; R7; R8; R9].


(** We model the following registers of the eBPF architecture. *)

Inductive preg :=
| IR : ireg -> preg  (**r integer registers *)
| PC : preg          (**r program counter *)  (*
| BP : preg          (**r base address register *) *)
.

Coercion IR: ireg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq.
Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).


Declare Scope asm.

(** Conventional names for stack pointer ([SP]) *)

Notation "'SP'" := R10 (only parsing) : asm.


(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the eBPF instructions set. See the eBPF
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

(** RFC9669: 3.1. Basic Instruction Encoding

- **offset**: signed integer offset used with pointer arithmetic, except where otherwise specified
(some arithmetic instructions reuse this field for other purposes)
- **imm**: signed integer immediate value

TODO: adding range of each field
*)
Definition off := Ptrofs.int. (* 16 bits *)
Definition imm := int. (* 32 bits *)


(** RFC9669: 4. Arithmetic and Jump Instructions
- For arithmetic and jump instructions (ALU, ALU64, JMP, and JMP32),

Note: here 
- `W32` represents 32-bit class (ALU + JMP32) and 
- `W64` represents 64-bit class (ALU64 + JMP)

And for each CompCert supported architecture, its Archi file has two information are useful
- `Archi.ptr64` represents the width of the current architecture
- `Archi.big_endian` represents the endianness of the current architecture
*)
Inductive width := W32 | W64.

(*
Definition warchi := if Archi.ptr64 then W64 else W32.
*)

(** RFC9669: 5. Load and Store Instructions

- **sz(size)**: The size modifier is one of: W/ H/ B/ DW
*)
Inductive sizeOp : Type :=
| Byte        (**r 1 byte *)
| HalfWord    (**r 2 bytes *)
| Word        (**r 4 bytes *)
| DBWord      (**r 8 bytes *)
.

Definition sizew (s:sizeOp) :=
  match s with
  | Byte | HalfWord | Word  => W32
  | DBWord => W64
  end.

(** RFC9669: 4.2. Byte Swap Instructions

- {END, LE, ALU}
- {END, BE, ALU}
- {END, TO, ALU64}
*)
Inductive endOp :=
  | LE32 (**r little endian, 32-bit *)
  | BE32 (**r big endian, 32-bit *)
  | LE64 (**r little endian, 64-bit *)
.

Inductive endSize :=
  | S16
  | S32
  | S64
.

(** For MOVSX instruction *)
Inductive signExtOp :=
  | SZ8
  | SZ16
  | SZ32
.

Definition signExtOp2Z (c: signExtOp): Z :=
  match c with
  | SZ8 => 8%Z
  | SZ16 => 16%Z
  | SZ32 => 32%Z
  end.

Inductive aluOp : Type :=
  | ADD                   (**r dst += src *)
  | SUB                   (**r dst -= src *)
  | MUL                   (**r dst *= src *)
  | DIV                   (**r dst /= src *)
  | SDIV                  (**r dst /= src (signed) *)
  | OR                    (**r dst |= src *)
  | AND                   (**r dst &= src *)
  | LSH                   (**r dst <<= src *)
  | RSH                   (**r dst >>= src (unsigned) *)
  | NEG                   (**r dst = ~dst *)
  | MOD                   (**r dst %= src *)
  | SMOD                  (**r dst %= src (signed) *)
  | XOR                   (**r dst ^= src *)
  | MOV                   (**r dst = src *)
  | MOVSX (c:signExtOp)   (**r dst = (s8/s16/s32) src *)
  | ARSH                  (**r dst >>= src (signed) *)
  | END (e:endOp) (s: endSize) (**r dst = bswap(16/32/64, dst) *)
.

Inductive cmpOp : Type :=
  | EQ: cmpOp                (**r e1 == e2 *)
  | NE: cmpOp                (**r e1 != e2 *)
  | SET: cmpOp               (**r e1 &  e2 *)
  | GT: signedness -> cmpOp  (**r e1 >  e2 *)
  | GE: signedness -> cmpOp  (**r e1 >= e2 *)
  | LT: signedness -> cmpOp  (**r e1 <  e2 *)
  | LE: signedness -> cmpOp. (**r e1 <= e2 *)

(***
  CALL      0x8    0x0      call helper function by static ID  {CALL, K, JMP} only, see `Helper functions`_
  CALL      0x8    0x1      call PC += imm                     {CALL, K, JMP} only, see `Program-local functions`_
  CALL      0x8    0x2      call helper function by BTF ID     {CALL, K, JMP} only, see `Helper functions`_
*)
Inductive call_type : Type :=
  | CallByStaticID
  | CallInternal
  | CallByBTF.

(***
  ADD       0x00   atomic add
  OR        0x40   atomic or
  AND       0x50   atomic and
  XOR       0xa0   atomic xor
*)
Inductive atomic_type : Type :=
  | AtomicADD (is_db: bool)
  | AtomicOR  (is_db: bool)
  | AtomicAND (is_db: bool)
  | AtomicXOR (is_db: bool)
  | AtomicXCHG (is_db: bool)
  | AtomicCMPXCHG (is_db: bool)
  | LOAD_ACQUIRE (sz:sizeOp)
  | STORE_RELEASE (sz:sizeOp)
  .

(***
src_reg Pseudocode imm Type dst Type
0x0 dst = (next_imm << 32) | imm integer integer
0x1 dst = map_by_fd(imm) map fd map
0x2 dst = map_val(map_by_fd(imm)) + next_imm map fd data address
0x3 dst = var_addr(imm) variable id data address
0x4 dst = code_addr(imm) integer code address
0x5 dst = map_by_idx(imm) map index map
0x6 dst = map_val(map_by_idx(imm)) + next_imm map index data address
*)
Inductive pseudo_ptr_ty :=
  | PSEUDO_Constant
  | PSEUDO_MAP_FD
  | PSEUDO_MAP_IDX
  | PSEUDO_MAP_VALUE
  | PSEUDO_MAP_IDX_VALUE
  | PSEUDO_BTF_ID
  | PSEUDO_FUNC
.

Inductive instruction : Type :=
  | Plddw  : forall (ty: pseudo_ptr_ty) (dst:ireg) (lo:imm) (hi:imm), instruction           (**r dst = lo | (hi <<32) *)

  | Ploadsx : forall (sz:sizeOp) (dst:ireg) (src:ireg) (offset:off), instruction            (**r dst = * (signed size) (src + offset) *)
  | Pload_probe : forall (sz:sizeOp) (dst:ireg) (src:ireg) (offset:off), instruction        (**r dst = if valid_ptr then * (unsigned size) (src + offset) *)
  | Ploadsx_probe : forall (sz:sizeOp) (dst:ireg) (src:ireg) (offset:off), instruction      (**r dst = if valid_ptr then * (unsigned size) (src + offset) *)
  | Pno_spec : instruction                                                                  (**r nop *)
  | Ptail_call : instruction                                                                (**r goto R2[R3] *)

  | Pload : forall (sz:sizeOp) (dst:ireg) (src:ireg) (offset:off), instruction              (**r dst = * (unsigned size) (src + offset) *)
  | Pstore : forall (sz:sizeOp) (dst:ireg) (src:ireg+imm) (offset:off), instruction         (**r * (unsigned size) (dst + offset) = src *)

  | Patomic: forall (aty: atomic_type) (dst:ireg) (src:ireg+imm) (offset:off), instruction  (**r atomic instructions *)

  | Palu : forall (op:aluOp) (w:width) (r:ireg) (a:ireg+imm), instruction                   (**r arithmetics *)

  | Pjmp32 : forall (immediate:imm), instruction                                            (**r 32-bit unconditional jump *)
  | Pjmp64 : forall (offset:off), instruction                                               (**r 64-bit unconditional jump *)
  | Pjmpcmp : forall (op:cmpOp) (w:width) (r:ireg) (a:ireg+imm) (offset:off), instruction   (**r conditional jump with comparison *)
  | Pcall : forall (cty: call_type) (immediate: imm), instruction                           (**r function call *)
  | Pret : instruction                                                                      (**r function return *)
.


Definition code := list int64 (*instruction *).
Record ebpf_prog := {
  main_code: code;
  jump_table: nat -> option code;
  max_entries: Z;
}.

Record function : Type := mkfunction {fn_sig: signature; fn_stksz: Z; fn_code: code}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.