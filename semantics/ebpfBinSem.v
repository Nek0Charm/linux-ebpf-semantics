From Coq Require Import List.

(** Abstract syntax and semantics for RISC-V assembly language. *)

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Locations.

From compcert Require Import Conventions Events Smallstep.
From compcert Require Stacklayout.
From compcert Require Import Op.

Import ListNotations.

(** * Abstract syntax *)

(** Registers. *)

(** RFC9559: TODO *)
Inductive ireg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.


Definition caller_saved_registers: list ireg := [R1; R2; R3; R4; R5].
Definition callee_saved_registers: list ireg := [R6; R7; R8; R9].


(** We model the following registers of the eBPF architecture. *)

Inductive preg :=
| IR : ireg -> preg  (**r integer registers *)
| PC : preg          (**r program counter *)
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
  | AtomicADD
  | AtomicOR
  | AtomicAND
  | AtomicXOR.

Inductive instruction : Type :=
  | Plddw  : forall (dst:ireg) (lo:imm) (hi:imm), instruction                             (**r dst = lo | (hi <<32) *)

  | Pload : forall (sz:sizeOp) (dst:ireg) (src:ireg) (offset:off), instruction            (**r dst = * (size) (src + offset) *)
  | Pstore : forall (sz:sizeOp) (dst:ireg) (src:ireg+imm) (offset:off), instruction       (**r * (size) (dst + offset) = src *)

  | Patomic: forall (aty: atomic_type) (w:width), instruction                             (**r atomic instructions *)

  | Palu : forall (o:aluOp) (w:width) (r:ireg) (a:ireg+imm), instruction                  (**r arithmetics *)

  | Pjmp32 : forall (immediate:imm), instruction                                          (**r 32-bit unconditional jump *)
  | Pjmp64 : forall (offset:off), instruction                                             (**r 64-bit unconditional jump *)
  | Pjmpcmp : forall (o:cmpOp) (w:width) (r:ireg) (a:ireg+imm) (offset:off), instruction  (**r conditional jump with comparison *)
  | Pcall : forall (cty: call_type) (immediate: imm), instruction                         (**r function call *)
  | Pret : instruction                                                                    (**r function return *)
.


Definition code := list byte (*instruction *).
Record function : Type := mkfunction {fn_sig: signature; fn_stksz: Z; fn_code: code}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(*
Definition dummy_function := mkfunction signature_main 0 nil. *)

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

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

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)
Variable find_instr: Z -> code -> option instruction.

(*
Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end. *)

  (*
(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.
*)

Variable ge: genv.

(**r give an immediate number for function ID, plus R1-R5 values as well as the current memory,
  returns a value for R0 and a new mem *)
Variable helper_function: imm -> val -> val -> val -> val -> val -> mem -> val * mem.


(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome : Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.


(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)
Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

(*
Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.
*)

Definition int64_of_int (i:int) := Int64.repr (Int.signed i).


Definition map_sum_left {A B A': Type} (F: A -> A')  (x: A+B) : A'+B :=
  match x with
  | inl i => inl (F i)
  | inr i => inr i
  end.

(**
   https://docs.cilium.io/en/latest/bpf/architecture/#instruction-set
 imm(ediate) is of signed type *)

Definition eval_reg_immw (w:width) (rs : regset) (ri: ireg+int) : val :=
  match ri with
  | inl i => rs i
  | inr i => match w with
             | W32 => Vint i
             | W64 => Vlong (int64_of_int i)
             end
  end.


Definition eval_val_int (w:width)  (ri: val+int) : val :=
  match ri with
  | inl i => i (** we assume each eBPF register is 64-bit: i.e.` Vlong vl` or `Vptr b ofs` *)
  | inr i => match w with
             | W32 => Vint i
             | W64 => Vlong (int64_of_int i)
                            (* constant are given a signed interpretation *)
             end
  end.

(** RFC9669: 4.1. Arithmetic Instructions 
      DIV 0x3 0 dst = (src != 0) ? (dst / src) : 0
      SDIV 0x3 1 dst = (src != 0) ? (dst s/ src) : 0

    fix: linux-doc-bpf
      DIV    0x3    0        dst = (src != 0) ? (dst / src) : 0
      SDIV   0x3    1        dst = (src == 0) ? 0 : ((src == -1 && dst == LLONG_MIN) ? LLONG_MIN : (dst s/ src))
  *)
  
Definition LLONG_MIN := Vlong (Int64.repr Int64.min_signed).
Definition INT_MIN := Vint (Int.repr Int.min_signed).

Definition eval_div_u32 (v1 v2:val) : val :=
  match Val.divu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 Vzero then Vzero else Vundef
  end.

Definition eval_div_s32 (v1 v2:val) : val :=
  match Val.divs v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 Vzero then Vzero
    else if (Val.eq v2 (Vint Int.mone)) && (Val.eq v1 INT_MIN) then INT_MIN
    else Vundef
  end.

Definition eval_div_u64 (v1 v2:val) : val :=
  match Val.divlu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 (Vlong Int64.zero) then Vlong Int64.zero else Vundef
  end.

Definition eval_div_s64 (v1 v2:val) : val :=
  match Val.divls v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 (Vlong Int64.zero) then  Vlong Int64.zero
    else if (Val.eq v2 (Vlong Int64.mone)) && (Val.eq v1 LLONG_MIN) then LLONG_MIN 
    else Vundef 
  end.

(** RFC9669: 4.1. Arithmetic Instructions 
      MOD 0x9 0 dst = (src != 0) ? (dst % src) : dst
      SMOD 0x9 1 dst = (src != 0) ? (dst s% src) : dst

    fix: linux-doc-bpf
      MOD    0x9    0        dst = (src != 0) ? (dst % src) : dst
      SMOD   0x9    1        dst = (src == 0) ? dst : ((src == -1 && dst == LLONG_MIN) ? 0: (dst s% src))
  *)
Definition eval_mod_u32 (v1 v2:val) : val :=
  match Val.modu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 Vzero then v1 else Vundef
  end.

Definition eval_mod_s32 (v1 v2:val) : val :=
  match Val.mods v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 Vzero then v1 
    else if (Val.eq v2 (Vint Int.mone)) && (Val.eq v1 INT_MIN) then Vzero
    else Vundef
  end.

Definition eval_mod_u64 (v1 v2:val) : val :=
  match Val.modlu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 (Vlong Int64.zero) then v1 else Vundef
  end.

Definition eval_mod_s64 (v1 v2:val) : val :=
  match Val.modls v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 (Vlong Int64.zero) then v1
    else if (Val.eq v2 (Vlong Int64.mone)) && (Val.eq v1 LLONG_MIN) then Vlong Int64.zero
    else Vundef
  end.

  (** RFC9669: 4.1. Arithmetic Instructions
      LSH 0x6 0 dst <<= (src & mask)
      RSH 0x7 0 dst >>= (src & mask)
      ARSH 0xc 0 sign extending (Section 2.3) dst >>= (src & mask)

    Note that: In the Coq formalization, we select to do mask for all ebPF shift instruction because the eBPF verifier guarantee the imm-based eBPF shift range checking.
    
    - In the core.c, it doesn't require the mask operations for the imm-based eBPF shift
    ```c
    // https://elixir.bootlin.com/linux/v6.17-rc4/source/kernel/bpf/core.c#L1790
    #define SHT(OPCODE, OP)					\
      ALU64_##OPCODE##_X:				\
        DST = DST OP (SRC & 63);		\
        CONT;					\
      ALU_##OPCODE##_X:				\
        DST = (u32) DST OP ((u32) SRC & 31);	\
        CONT;					\
      ALU64_##OPCODE##_K:				\
        DST = DST OP IMM;			\
        CONT;					\
      ALU_##OPCODE##_K:				\
        DST = (u32) DST OP (u32) IMM;		\
        CONT;
    ``` 
    - But the verifier.c statically checks the range of imm-based shift value.
    ```c
    //https://elixir.bootlin.com/linux/v6.17-rc4/source/kernel/bpf/verifier.c#L15770
    		if ((opcode == BPF_LSH || opcode == BPF_RSH ||
		     opcode == BPF_ARSH) && BPF_SRC(insn->code) == BPF_K) {
			int size = BPF_CLASS(insn->code) == BPF_ALU64 ? 64 : 32;

			if (insn->imm < 0 || insn->imm >= size) {
				verbose(env, "invalid shift %d\n", insn->imm);
				return -EINVAL;
			}
		}
    ```
  *)
Definition eval_shift_mask (w:width) (v1:val) : val :=
  match w with
  | W32 => Val.and v1 (Vint (Int.repr 31%Z))
  | W64 => Val.andl v1 (Vlong (Int64.repr 63%Z))
  end.

(** RFC9669: 4.1. Arithmetic Instructions 
      MOV 0xb 0 dst = src
      MOVSX 0xb 8/16/32 dst = (s8,s16,s32)src
  *)
Definition eval_movsx (w:width) (c: signExtOp) (v2 :val) : val :=
  match w with
  | W32 => Val.longofintu (Val.sign_ext (signExtOp2Z c) v2)
  | W64 => Val.sign_ext_l (signExtOp2Z c) v2
  end.

(** RFC9669: 4.1. Arithmetic Instructions
      END 0xd 0 byte swap operations (see Section 4.2)
  *)
Definition swab16 (i: int64): int64 :=
  let i0 := Int64.unsigned_bitfield_extract 0 8 i in
  let i1 := Int64.unsigned_bitfield_extract 8 8 i in
    Int64.bitfield_insert 8 8 i1 i0.

(*
Compute (swab16 (Int64.repr 0x3412)). (**r 4660 *)
Compute 0x1234. (**r 4660 *)
Compute 0x3412. (**r 13330 *) *)

Definition swab32 (i: int64): int64 :=
  let i0 := Int64.unsigned_bitfield_extract 0 8 i in
  let i1 := Int64.unsigned_bitfield_extract 8 8 i in
  let i2 := Int64.unsigned_bitfield_extract 16 8 i in
  let i3 := Int64.unsigned_bitfield_extract 24 8 i in
    Int64.bitfield_insert 24 8
      (Int64.bitfield_insert 16 8
        (Int64.bitfield_insert 8 8 i3 i2) i1) i0.

(*
Compute (swab32 (Int64.repr 0x12345678)). (**r 2018915346 *)
Compute 0x12345678. (**r 305419896 *)
Compute 0x78563412. (**r 2018915346 *) *)

Definition swab64 (i: int64): int64 :=
  let i0 := Int64.unsigned_bitfield_extract 0 8 i in
  let i1 := Int64.unsigned_bitfield_extract 8 8 i in
  let i2 := Int64.unsigned_bitfield_extract 16 8 i in
  let i3 := Int64.unsigned_bitfield_extract 24 8 i in
  let i4 := Int64.unsigned_bitfield_extract 32 8 i in
  let i5 := Int64.unsigned_bitfield_extract 40 8 i in
  let i6 := Int64.unsigned_bitfield_extract 48 8 i in
  let i7 := Int64.unsigned_bitfield_extract 56 8 i in
    Int64.bitfield_insert 56 8
      (Int64.bitfield_insert 48 8
        (Int64.bitfield_insert 40 8
          (Int64.bitfield_insert 32 8
            (Int64.bitfield_insert 24 8
              (Int64.bitfield_insert 16 8
                (Int64.bitfield_insert 8 8 i7 i6) i5) i4) i3) i2) i1) i0.

(*
Compute (swab64 (Int64.repr 0x1234567890abcdef)). (**r 17279655982273016850 *)
Compute 0x1234567890abcdef. (**r 1311768467294899695 *)
Compute 0xefcdab9078563412. (**r 17279655982273016850 *) *)

Definition swapn (s: endSize) :=
  match s with
  | S16 => swab16
  | S32 => swab32
  | S64 => swab64
  end.

Definition eval_end (e:endOp) (s: endSize) (v: val) : val :=
  match v with
  | Vlong vl => Vlong
    match e with
    | LE32 => if Archi.big_endian then (swapn s) vl else vl
    | BE32 => if Archi.big_endian then vl else (swapn s) vl
    | LE64 => (swapn s) vl
    end
  | _ => Vundef
  end.

(** Evaluation of [Palu] operands *)
Definition eval_alu32 (b: aluOp) (v1: val) (v2: val+int) : val :=
  let dst := Val.loword v1 in
  let src := match v2 with | inl r => Val.loword r | inr i => Vint i end in
    match b with
    | ADD   => Val.longofintu (Val.add dst src)
    | SUB   => Val.longofintu (Val.sub dst src)
    | MUL   => Val.longofintu (Val.mul dst src)
    | DIV   => Val.longofintu (eval_div_u32 dst src)
    | SDIV  => Val.longofint  (eval_div_s32 dst src)
    | OR    => Val.longofintu (Val.or dst src)
    | AND   => Val.longofintu (Val.and dst src)
    | LSH   => Val.longofintu (Val.shl dst (eval_shift_mask W32 src))
    | RSH   => Val.longofintu (Val.shru dst (eval_shift_mask W32 src))
    | NEG   => Val.longofintu (Val.neg dst)
    | MOD   => Val.longofintu (eval_mod_u32 dst src)
    | SMOD  => Val.longofint  (eval_mod_s32 dst src)
    | XOR   => Val.longofintu (Val.xor  dst src)
    | MOV   => Val.longofintu src
    | MOVSX c => eval_movsx W32 c src
    | ARSH  => Val.longofintu (Val.shr dst (eval_shift_mask W32 src))
    | END e s => eval_end e s dst
    end.

Definition eval_alu64 (b: aluOp) (dst: val) (v2: val+int) : val :=
  let src := eval_val_int W64 v2 in
  match b with
  | ADD   => Val.addl dst src
  | SUB   => Val.subl dst src
  | MUL   => Val.mull dst src
  | DIV   => eval_div_u64 dst src
  | SDIV  => eval_div_s64 dst src
  | OR    => Val.orl dst src
  | AND   => Val.andl dst src
  | LSH   => Val.shll dst (eval_shift_mask W64 src)
  | RSH   => Val.shrlu dst (eval_shift_mask W64 src)
  | NEG   => Val.negl dst
  | MOD   => eval_mod_u64 dst src
  | SMOD  => eval_mod_s64 dst src
  | XOR   => Val.xorl dst src
  | MOV   => src
  | MOVSX c => eval_movsx W64 c src
  | ARSH  => Val.shrl dst (eval_shift_mask W64 src)
  | END e s => eval_end e s dst
  end.

Definition exec_alu (o: aluOp) (w:width) (r: ireg) (ri: ireg+int) (rs: regset) (m: mem) :=
  let alu_f := match w with | W32 => eval_alu32 | W64 => eval_alu64 end in
  let v := alu_f o (rs#r) (map_sum_left (fun (x:ireg) => rs#x) ri) in
    Next (nextinstr (rs#r <- v)) m.

(** RFC9669: 4.3. Jump Instructions

  ========  =====  =======  =================================  ===================================================
  code      value  src_reg  description                        notes
  ========  =====  =======  =================================  ===================================================
  JA        0x0    0x0      PC += offset                       {JA, K, JMP} only
  JA        0x0    0x0      PC += imm                          {JA, K, JMP32} only
  JEQ       0x1    any      PC += offset if dst == src
  JGT       0x2    any      PC += offset if dst > src          unsigned
  JGE       0x3    any      PC += offset if dst >= src         unsigned
  JSET      0x4    any      PC += offset if dst & src
  JNE       0x5    any      PC += offset if dst != src
  JSGT      0x6    any      PC += offset if dst > src          signed
  JSGE      0x7    any      PC += offset if dst >= src         signed
  JLT       0xa    any      PC += offset if dst < src          unsigned
  JLE       0xb    any      PC += offset if dst <= src         unsigned
  JSLT      0xc    any      PC += offset if dst < src          signed
  JSLE      0xd    any      PC += offset if dst <= src         signed
  ========  =====  =======  =================================  ===================================================
*)
Definition eval_cmp32 (op: cmpOp) (rs: regset) (m: mem) (r: ireg) (ri: ireg+imm) : option bool :=
  let dst := Val.loword (rs#r) in
  let src := match ri with | inl r => Val.loword (rs#r) | inr i => Vint i end in
    match op with
    | EQ          => Val.cmpu_bool (Mem.valid_pointer m) Ceq dst src
    | GT Signed   => Val.cmp_bool Cgt dst src
    | GT Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cgt dst src
    | GE Signed   => Val.cmp_bool Cge dst src
    | GE Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cge dst src
    | LT Signed   => Val.cmp_bool Clt dst src
    | LT Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Clt dst src
    | LE Signed   => Val.cmp_bool Cle dst src
    | LE Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cle dst src
    | SET         => Val.cmpu_bool (Mem.valid_pointer m) Cne (Val.and dst src) (Vint Int.zero)
    | NE          => Val.cmpu_bool (Mem.valid_pointer m) Cne dst src
    end.

Definition eval_cmp64 (op: cmpOp) (rs: regset) (m: mem) (r: ireg) (ri: ireg+imm) : option bool :=
  let dst := rs#r in
  let src := match ri with | inl r => rs#r | inr i => Vlong (int64_of_int i) end in
    match op with
    | EQ          => Val.cmplu_bool (Mem.valid_pointer m) Ceq dst src
    | GT Signed   => Val.cmpl_bool Cgt dst src
    | GT Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Cgt dst src
    | GE Signed   => Val.cmpl_bool Cge dst src
    | GE Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Cge dst src
    | LT Signed   => Val.cmpl_bool Clt dst src
    | LT Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Clt dst src
    | LE Signed   => Val.cmpl_bool Cle dst src
    | LE Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Cle dst src
    | SET         => Val.cmplu_bool (Mem.valid_pointer m) Cne (Val.and dst src) (Vint Int.zero)
    | NE          => Val.cmplu_bool (Mem.valid_pointer m) Cne dst src
    end.

Definition exec_jmp32 (i: imm) (rs: regset) (m:mem) :=
  Next (nextinstr (rs#PC <- (Val.offset_ptr (rs PC) (Ptrofs.of_int i)))) m.

Definition exec_jmp64 (o: off) (rs: regset) (m:mem) :=
  Next (nextinstr (rs#PC <- (Val.offset_ptr (rs PC) o))) m.

Definition exec_jmpcmp (w: width) (op: cmpOp) (r: ireg) (ri: ireg+imm) (o: off) (rs: regset) (m:mem) :=
  match
    match w with
    | W32 => eval_cmp32 op rs m r ri
    | W64 => eval_cmp64 op rs m r ri
    end with
  | None => Stuck
  | Some cond => 
    let rs' := if cond then rs#PC <- (Val.offset_ptr (rs PC) o) else rs in
      Next (nextinstr rs') m
  end.

(** Auxiliaries for memory accesses *)

(*Definition size_to_memory_chunk (size: sizeOp) : memory_chunk :=
  match size with
  | Byte => Mint8unsigned
  | HalfWord => Mint16unsigned
  | Word => Many32
  | SignedWord => Mint32
  end.
 *)

 (** The global memory model for all eBPF programs, it splits into:
 - local memory, like eBPF stack or program-local array, only accessed by eBPF load/store instructions
 - shared memory, like map, hashmap, only accessed by eBPF atomic instructions
 *)
Record gmem := {
  m: mem; (** the CompCert memory model *)
  local_blks: list block; (** eBPF stack + context + ... *)
  (* share_blks: list block; (** eBPF map + ... *) *)
  mtest: memory_chunk -> mem -> block -> Z -> bool; (** simular to load/store, 
    check the specified region (val, chunk) in the shared memory whether the race-condition occurs *)
  local_blks_wf: forall m b, List.In b local_blks -> Mem.valid_block m b;  (** local blocks are valid in the memory *)
  (*share_blks_wf: forall m b, List.In b share_blks -> Mem.valid_block m b;  (** share blocks are valid in the memory *)
  share_local_disjoint: forall b, List.In b share_blks <-> ~(List.In b local_blks);  (** share blocks and local blocks are disjoint *)
  mtest_wf: forall mc m b ofs res,   (** if a block is shared (i.e. not local) and valid in the memory, mtest returns *)
    mtest mc m b ofs = res ->
      Mem.valid_pointer m b ofs = true /\ List.In b share_blks; *)
  mtest_wf: forall mc m b ofs res,   (** we only test the shared (i.e. not local) memory regions *)
    mtest mc m b ofs = res ->
      Mem.valid_pointer m b ofs = true /\ ~(List.In b local_blks);
}.

Definition load (k: sizeOp) (addr:val) (m:mem) :=
  match k with
  | Byte => Mem.loadv Mint8unsigned m addr
  | HalfWord => Mem.loadv Mint16unsigned m addr
  | Word     => Mem.loadv Mint32 m addr
  | DBWord     => if Archi.ptr64 then Mem.loadv Mint64 m addr else None
  end.

Definition exec_load (k: sizeOp) (r:ireg) (r':ireg) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match load k (Val.offset_ptr rs#r' o) m with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition store (k: sizeOp) (addr:val) (v:val) (m:mem) :=
  match k with
  | Byte => Mem.storev Mint8unsigned m addr v
  | HalfWord => Mem.storev Mint16unsigned m addr v
  | Word     => Mem.storev Mint32 m addr v
  | DBWord     => if Archi.ptr64 then Mem.storev Mint64 m addr v else None
  end.

Definition exec_store (k: sizeOp) (r:ireg) (ri:ireg+int) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match store  k (Val.offset_ptr rs#r o) (eval_reg_immw (sizew k) rs ri) m with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition exec_lddw (r:ireg) (lo hi: imm) (rs: regset) (m:mem) :=
  let v := Vlong (Int64.ofwords hi  lo) in
    Next (nextinstr (nextinstr (rs#r <- v))) m.

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    match r with
    | R6 | R7 | R8 | R9 | R10 => rs r
    | _ => Vundef
    end.


(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

Definition exec_instr (f: function) (i: instruction) (rs:regset) (m: mem) : outcome :=
  match i with
  | Plddw r lo hi       => exec_lddw r lo hi rs m
  | Pload k r r' o   => exec_load k r r' o rs m
  | Pstore k r ri o  => exec_store k r ri o rs m
  | Palu o w r ri      => exec_alu o w r ri rs m
  | Pjmp32 o     => exec_jmp32 o rs m
  | Pjmp64 i     => exec_jmp64 i rs m
  | Pjmpcmp op w r ri o => exec_jmpcmp w op r ri o rs m (*
  | Pcall CallInternal i => exec_call_internal i rs m *)
  
  (*
  | Pcall (inr s) sg => Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
                                #PC <- (Genv.symbol_address ge s Ptrofs.zero)
                          ) m
  | Pcall cty imm => Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
                               #PC  <- (rs#r)) m *)
  | Pret             => Next rs m
  | _                => Stuck
  end.


(** Undefine all registers except SP, BP and callee-save registers *)
(*
Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r BP || preg_eq r R10
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use eBPF registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#BP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).
*)

(** Execution of the instruction at [rs PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m') (*
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs BP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m') *)
      .

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
          # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
          # R10 <- Vnullptr
          # BP  <- Vnullptr
          # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs R0 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR R10 => false
  | IR _ => true
  | FR _ => true
  | PC   => false
  | RA   => false
  end.

(* data_preg_sp includes R10 *)
Definition data_preg_sp (r: preg) : bool :=
  match r with
  | IR _ => true
  | FR _ => true
  | PC   => false
  | RA   => false
  end.
  *)