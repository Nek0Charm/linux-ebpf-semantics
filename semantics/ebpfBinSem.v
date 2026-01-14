From Coq Require Import List.

(** Abstract syntax and semantics for RISC-V assembly language. *)

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.  (*
From compcert.common Require Import Globalenvs. *) (*
From compcert Require Import Locations. *)

From compcert Require Import Conventions Events Smallstep.
From compcert Require Stacklayout.
From compcert Require Import Op.

Import ListNotations.

(** * Abstract syntax *)

(** Registers. *)

(** RFC9559: TODO *)
Inductive ireg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 
  | R10 (**r eBPF stack frame pointer *).

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.


Definition caller_saved_registers: list ireg := [R1; R2; R3; R4; R5].
Definition callee_saved_registers: list ireg := [R6; R7; R8; R9].


(** We model the following registers of the eBPF architecture. *)

Inductive preg :=
| IR : ireg -> preg  (**r integer registers *)
| PC : preg          (**r program counter *)
| BP : preg          (**r base address register *)
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

  | Patomic: forall (aty: atomic_type) (w:width) (dst:ireg) (src:ireg+imm) (offset:off), instruction  (**r atomic instructions *)

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

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)
Variable find_instr: Z -> code -> option instruction.

(*
Variable ge: genv.
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

(*
Variable ge: genv. *)

(*
Record cstk' := mk_cstk' {
  stk_ra: val;
  stk_r6: val;
  stk_r7: val;
  stk_r8: val;
  stk_r9: val;  
}.

Definition cstk := list cstk'. *)

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome : Type :=
  | Next: regset -> mem -> outcome (*
  | Stop: val -> outcome *)
  | Stuck: outcome.

(**r give an immediate number for function ID, plus R1-R5 values as well as the current memory,
  returns a value for R0 and a new global mem *)
Variable ebpf_call_function:
  imm -> val -> val -> val -> val -> val -> outcome -> option (val * mem).


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

Definition exec_jmp32 (i: imm) (rs: regset) (m: mem) :=
  Next (nextinstr (rs#PC <- (Val.offset_ptr (rs PC) (Ptrofs.of_int i)))) m.

Definition exec_jmp64 (o: off) (rs: regset) (m: mem) :=
  Next (nextinstr (rs#PC <- (Val.offset_ptr (rs PC) o))) m.

Definition exec_jmpcmp (w: width) (op: cmpOp) (r: ireg) (ri: ireg+imm) (o: off) (rs: regset) (m: mem) :=
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


Definition load (k: sizeOp) (addr:val) (m: mem) :=
  match k with
  | Byte => Mem.loadv Mint8unsigned m addr
  | HalfWord => Mem.loadv Mint16unsigned m addr
  | Word     => Mem.loadv Mint32 m addr
  | DBWord     => if Archi.ptr64 then Mem.loadv Mint64 m addr else None
  end.

Definition exec_load (k: sizeOp) (r:ireg) (r':ireg) (o:Ptrofs.int) (rs: regset) (m: mem) :=
  match load k (Val.offset_ptr rs#r' o) m with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition store (k: sizeOp) (addr:val) (v:val) (m: mem) :=
  match k with
  | Byte => Mem.storev Mint8unsigned m addr v
  | HalfWord => Mem.storev Mint16unsigned m addr v
  | Word     => Mem.storev Mint32 m addr v
  | DBWord     => if Archi.ptr64 then Mem.storev Mint64 m addr v else None
  end.

Definition exec_store (k: sizeOp) (r:ireg) (ri:ireg+int) (o:Ptrofs.int) (rs: regset) (m: mem) :=
  match store  k (Val.offset_ptr rs#r o) (eval_reg_immw (sizew k) rs ri) m with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition exec_lddw (r:ireg) (lo hi: imm) (rs: regset) (m: mem) :=
  let v := Vlong (Int64.ofwords hi  lo) in
    Next (nextinstr (nextinstr (rs#r <- v))) m.

(** Undefine all ebpf caller-saved registers: i.e. R1 to R5 *)
Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    match r with
    | R1 | R2 | R3 | R4 | R5 => Vundef
    | _ => rs r
    end.

(** Undefine all ebpf registers except caller-saved registers (i.e. R1 to R5) and R10 *)
Definition def_caller_save_regs (rs: regset) : regset :=
  fun r =>
    match r with
    | R1 | R2 | R3 | R4 | R5 | R10 | BP => rs r
    | _ => Vundef
    end.

Definition spilling_callee_save_registers (ofs_r6 ofs_r7 ofs_r8 ofs_r9: ptrofs)
  (bp: val) (rs: regset) (m1: mem): option mem := 
  match Mem.storev Mptr m1 (Val.offset_ptr bp ofs_r6) rs#R6 with
  | None => None
  | Some m2 =>
    match Mem.storev Mptr m2 (Val.offset_ptr bp ofs_r7) rs#R7 with
    | None => None
    | Some m3 =>
      match Mem.storev Mptr m3 (Val.offset_ptr bp ofs_r8) rs#R8 with
      | None => None
      | Some m4 => Mem.storev Mptr m4 (Val.offset_ptr bp ofs_r9) rs#R9
      end
    end
  end.

Definition stack_offset (z:Z) :=
  Ptrofs.repr (z - 6*8). (**r RA + SP + R6 + R7 + R8 + R9 *)

(**r The thread-local eBPF memory layout is:

| ....     |
------------ <-- New BP when internal call occurs
|  old_r9  |
------------ <-- R10 + 5*8
|  old_r8  |
------------ <-- R10 + 4*8
|  old_r7  |
------------ <-- R10 + 3*8
|  old_r6  |
------------ <-- R10 + 2*8
|  old_sp  |
------------ <-- R10 + 1*8
|  old_ra  |
------------ <-- R10 or SP
|          |
| 512Byte  |
|          |
------------ <-- BP


**)

Definition alloc_frame (sz: Z) (ofs_link ofs_ra ofs_r6 ofs_r7 ofs_r8 ofs_r9: ptrofs)
  (rs: regset) (m: mem): option (regset * mem) := 
  let (m1, stk) := Mem.alloc m 0 sz in
  let bp := (Vptr stk Ptrofs.zero) in
  let sp := Val.offset_ptr bp (stack_offset sz) in
  let ra := Val.offset_ptr rs#PC Ptrofs.one in
    match Mem.storev Mptr m1 (Val.offset_ptr bp ofs_link) rs#BP with
    | None => None
    | Some m2 =>
      match Mem.storev Mptr m2 (Val.offset_ptr bp ofs_ra) ra with
      | None => None
      | Some m3 =>
        match spilling_callee_save_registers ofs_r6 ofs_r7 ofs_r8 ofs_r9 bp rs m3 with
        | None => None
        | Some m4 => Some (nextinstr (rs #R10 <- sp #BP <- bp), m4)
        end
      end
    end.

Definition exec_call_internal (i: imm) (rs: regset) (m: mem) :=
  let target_pc := Val.offset_ptr (Val.offset_ptr (rs PC) (Ptrofs.of_int i)) Ptrofs.one in
    match alloc_frame (512+6*8) (Ptrofs.repr (512+0*8)) (Ptrofs.repr (512+1*8))
      (Ptrofs.repr (512+2*8)) (Ptrofs.repr (512+3*8)) (Ptrofs.repr (512+4*8)) (Ptrofs.repr (512+5*8)) rs m with
    | None => Stuck
    | Some (rs', m') => Next (def_caller_save_regs rs')#PC <- target_pc m'
    end.

Definition reload_callee_save_registers (ofs_r6 ofs_r7 ofs_r8 ofs_r9: ptrofs)
  (bp: val) (rs: regset) (m: mem): option regset := 
  match Mem.loadv Mptr m (Val.offset_ptr bp ofs_r6) with
  | None => None
  | Some v6 =>
    match Mem.loadv Mptr m (Val.offset_ptr bp ofs_r7) with
    | None => None
    | Some v7 =>
      match Mem.loadv Mptr m (Val.offset_ptr bp ofs_r8) with
      | None => None
      | Some v8 => 
        match Mem.loadv Mptr m (Val.offset_ptr bp ofs_r9) with
        | None => None
        | Some v9 => Some (rs#R6 <- v6 #R7 <- v7 #R8 <- v8 #R9 <- v9)
        end
      end
    end
  end.

Definition free_frame (sz: Z) (ofs_link ofs_ra ofs_r6 ofs_r7 ofs_r8 ofs_r9: ptrofs)
  (rs: regset) (m: mem): option (regset * mem) :=
  match Mem.loadv Mptr m (Val.offset_ptr rs#BP ofs_ra) with
  | None => None
  | Some ra =>
    match Mem.loadv Mptr m (Val.offset_ptr rs#BP ofs_link) with
    | None => None
    | Some bp =>
      match reload_callee_save_registers ofs_r6 ofs_r7 ofs_r8 ofs_r9 rs#BP rs m with
      | None => None
      | Some rs' =>
        match rs'#BP with
        | Vptr stk ofs =>
          match Mem.free m stk 0 sz with
          | None => None
          | Some m' =>
            let sp := Val.offset_ptr bp (stack_offset sz) in
              Some (nextinstr (rs'#R10 <- sp #BP <- bp #PC <- ra), m')
          end
        |  _   => None
        end
      end
    end
  end.

Definition exec_ret (rs: regset) (m: mem) :=
  match free_frame (512+6*8) (Ptrofs.repr (512+0*8)) (Ptrofs.repr (512+1*8))
      (Ptrofs.repr (512+2*8)) (Ptrofs.repr (512+3*8)) (Ptrofs.repr (512+4*8)) (Ptrofs.repr (512+5*8)) rs m with
  | None => Stuck
  | Some (rs', m') => Next (undef_caller_save_regs rs') m'
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

Definition exec_instr (i: instruction) (rs:regset) (m: mem) : outcome :=
  match i with
  | Plddw r lo hi         => exec_lddw r lo hi rs m
  | Pload k r r' o        => exec_load k r r' o rs m
  | Pstore k r ri o       => exec_store k r ri o rs m
  | Palu o w r ri         => exec_alu o w r ri rs m
  | Pjmp32 o              => exec_jmp32 o rs m
  | Pjmp64 i              => exec_jmp64 i rs m
  | Pjmpcmp op w r ri o   => exec_jmpcmp w op r ri o rs m
  | Pcall CallInternal i  => exec_call_internal i rs m
  | Pret                  => exec_ret rs m
  | _                     => Stuck
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

Inductive eBPF_event : Set :=
  | eBPF_vload
  | eBPF_vstore
  | eBPF_ext_call
  | eBPF_atomic
  | eBPF_switch.

Definition etrace := list eBPF_event.
Definition eE0: list eBPF_event := nil.

Definition exec_instr_event (i: instruction) : etrace :=
  match i with
  | Pload k r r' o        => [eBPF_vload]
  | Pstore k r ri o       => [eBPF_vstore]
  | _                     => eE0
  end.

Inductive step (c: code): state -> etrace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs i rs m rs' m' et,
      rs PC = Vptr b ofs ->
      find_instr (Ptrofs.unsigned ofs) c = Some i ->
      exec_instr i rs m = Next rs' m' ->
      exec_instr_event i = et ->
      step c (State rs m) et (State rs' m')
  | exec_step_external:
      forall b ofs cty i res rs m rs' m',
      rs PC = Vptr b ofs ->
      find_instr (Ptrofs.unsigned ofs) c = Some (Pcall cty i) ->
      cty = CallByBTF \/ cty = CallByStaticID ->
      ebpf_call_function i rs#R1 rs#R2 rs#R3 rs#R4 rs#R5 (Next rs m) = Some (res, m') -> (**r an ebpf call may invoke another ebpf program that modifies the global memory *)
      rs' = nextinstr (undef_caller_save_regs rs)
                #R0 <- res
                #PC <- (Val.offset_ptr (rs#PC) Ptrofs.one) ->
      step c (State rs m) [eBPF_ext_call] (State rs' m') (*
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m') *)
      .


Inductive initial_state (p: program) (blk stk: block): state -> Prop :=
  | initial_state_intro: forall m0,
      let rs0 :=
        (Pregmap.init Vundef)
          # PC <- (Vptr blk Ptrofs.zero)
          # R10 <- (Vptr stk Ptrofs.zero)
          # BP  <- Vnullptr in
      (forall i, 0<= i -> i < 512+6*8 -> Mem.valid_access m0 Mint8unsigned stk i Freeable) -> (**r access to [0, 512*8) *)
      (forall i, 0<= i -> i < 512 \/ (i <= 512+2*8 /\ i < 512+6*8) -> Mem.load Mint8unsigned m0 blk i = Some Vundef) -> (**r the init content of [0, 512) + r6-r9 are all Vundef *)
      Mem.load Mint64 m0 blk 512 = Some Vnullptr -> (**r the init old_ra is Vnullptr *)
      Mem.load Mint64 m0 blk (512+1*8) = Some Vnullptr -> (**r the init old_sp is Vnullptr *)
      initial_state p blk stk (State rs0 m0).

Inductive final_state: state -> int64 -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs R0 = Vlong r ->
      final_state (State rs m) r.


 (** The global memory model for all eBPF programs, it splits into:
 - local memory, like eBPF stack or program-local array, only accessed by eBPF load/store instructions
 - shared memory, like map, hashmap, only accessed by eBPF atomic instructions
 *)
Definition tid := nat.

Record ThreadPool := {
  tp_map: tid -> option (regset * block);
  next_tid : tid;
}.

Record ProgConfig := mkBuild_ProgConfig {
  thread_pool : ThreadPool;
  cur_tid     : tid;
  gm          : mem;
  atom_bit    : bool; (*r true -> In atomic zone; false -> NOT-IN atomic zone *)
}.

Variable env : block -> code.

Definition update_core (tp: ThreadPool) (t: tid) (r: regset): ThreadPool :=
{|
  tp_map :=
    fun i =>
      if Nat.eqb i t then
        match (tp_map tp) t with
        | None => None
        | Some (_, b) => Some (r, b)
        end
      else
        (tp_map tp) i;
  next_tid := next_tid tp
|}.


Definition atomic_fun (w: width) (aty: atomic_type) :=
  match aty with
  | AtomicADD => match w with W32 => Val.add | W64 => Val.addl end
  | AtomicOR => match w with W32 => Val.or | W64 => Val.orl end
  | AtomicXOR => match w with W32 => Val.xor | W64 => Val.xorl end
  | AtomicAND => match w with W32 => Val.and | W64 => Val.andl end
  end.

Definition chunk_of_width (w: width) :=
  match w with
  | W32 => Mint32
  | W64 => Mint64
  end.

Definition exec_atomic_store (w: width) (aty: atomic_type) (dst src: ireg) (o : off) (rs:regset) (m: mem): outcome :=
  let addr := Val.offset_ptr (rs dst) o in
  let sv := match w with W32 => Val.loword (rs src) | W64 => rs src end in
    match Mem.loadv (chunk_of_width w) m addr with
    | None => Stuck
    | Some v =>
      let res := (atomic_fun w aty v sv) in
        match Mem.storev (chunk_of_width w) m addr res with
        | None => Stuck
        | Some m' => Next (nextinstr rs) m'
        end
    end.

Definition exec_atomic (w: width) (aty: atomic_type) (dst: ireg) (src: ireg+imm) (o : off) (rs:regset) (m: mem): outcome :=
  match src with
  | inl r => exec_atomic_store w aty dst r o rs m
  | _ => Stuck
  end. 

Definition exec_atomic_instr_event (aty: atomic_type): etrace :=
  [eBPF_vload].

Inductive atomic_step (c: code): state -> etrace -> state -> Prop :=
  | exec_atomic_step:
      forall b ofs rs m rs' m' et aty w dst src o,
      rs PC = Vptr b ofs ->
      find_instr (Ptrofs.unsigned ofs) c = Some (Patomic aty w dst src o) ->
      exec_atomic w aty dst src o rs m = Next rs' m' ->
      exec_atomic_instr_event aty = et ->
        atomic_step c (State rs m) et (State rs' m').   


Inductive gstep: ProgConfig -> etrace -> ProgConfig -> Prop :=
  | Core_step: forall tp cid gm d et rs tp' rs' gm' blk,
    (tp_map tp) cid = Some (rs, blk) ->
    update_core tp cid rs' = tp' ->
    step (env blk) (State rs gm) et (State rs' gm') ->
      gstep (mkBuild_ProgConfig tp cid gm d) et 
            (mkBuild_ProgConfig tp' cid gm' d)

  | Switch_step: forall tp cid gm d cid' s s',
    (tp_map tp) cid = Some s -> (* valid eBPF thread id *)
    (tp_map tp) cid' = Some s' -> (* valid eBPF thread id *)
      gstep (mkBuild_ProgConfig tp cid gm d) [eBPF_switch]
            (mkBuild_ProgConfig tp cid' gm d)

  | Atomic_step: forall tp cid gm d et rs tp' rs' gm' blk,
    (tp_map tp) cid = Some (rs, blk) ->
    atomic_step (env blk) (State rs gm) et (State rs' gm') ->
      gstep (mkBuild_ProgConfig tp cid gm d) et 
            (mkBuild_ProgConfig tp' cid gm' d)
.
  | Callstep: 
            
.


End RELSEM.


Inductive thread_state :=
  | TState: regset -> cstk -> thread_state.

Fixpoint update_error {A:Type} (l:list A) (n:nat) (v: A) {struct n} : option (list A) :=
  match n, l with
    | O, x :: tl => Some (v::tl)
    | S n, x :: tl => 
      match update_error tl n v with
      | None => None
      | Some rl => Some (x::rl)
      end
    | _, _ => None
  end.

Inductive gstep (l: list code) : list thread_state -> mem -> etrace -> list thread_state -> mem -> Prop :=
  | Gstep_thread_next: forall n c ts m rs stk t ts' m' rs' stk',
    List.nth_error l n = Some c ->
    List.nth_error ts n = Some (TState rs stk) ->
    step c (State rs stk m) t (State rs' stk' m') ->
    update_error ts n (TState rs' stk') = Some ts' ->
      gstep l ts m t ts' m'
  | Gstep_thread_stop: forall n c ts m rs stk t res,
    List.nth_error l n = Some c ->
    List.nth_error ts n = Some (TState rs stk) ->
    step c (State rs stk m) t (Return res) ->
      gstep l ts m t ts m
    .

Record gstate := mkgstate {
  gm: mem; (** the CompCert memory model *)
  grs: block -> regset;
  local_blks: list block; (** eBPF stack + context + ... *)
  (* share_blks: list block; (** eBPF map + ... *) *)
  mtest: memory_chunk -> mem -> block -> Z -> bool; (** simular to load/store, 
    check the specified region (val, chunk) in the shared memory whether the race-condition occurs *) (*
  local_blks_wf: forall b, List.In b local_blks -> Mem.valid_block gm b;  *)
  (*share_blks_wf: forall m b, List.In b share_blks -> Mem.valid_block m b;  (** share blocks are valid in the memory *)
  share_local_disjoint: forall b, List.In b share_blks <-> ~(List.In b local_blks);  (** share blocks and local blocks are disjoint *)
  mtest_wf: forall mc m b ofs res,   (** if a block is shared (i.e. not local) and valid in the memory, mtest returns *)
    mtest mc m b ofs = res ->
      Mem.valid_pointer m b ofs = true /\ List.In b share_blks; *) (*
  mtest_wf: forall mc b ofs res,   (** we only test the shared (i.e. not local) memory regions *)
    mtest mc gm b ofs = res ->
      Mem.valid_pointer gm b ofs = true /\ ~(List.In b local_blks); *)
}.

(* Inductive gstate :=
  | GState: mem -> (block -> regset) -> list block -> 
    (memory_chunk -> mem -> block -> Z -> bool) -> gstate. *)

(** local blocks are valid in the memory *)
(* Definition gstate_wf (gst: gstate) :=
  match gst with
  | GState gm grs local_blks mtest => 
    forall b, List.In b local_blks -> Mem.valid_block gm b /\
    forall mc b ofs res,   (** we only test the shared (i.e. not local) memory regions *)
      mtest mc gm b ofs = res ->
        Mem.valid_pointer gm b ofs = true /\ ~(List.In b local_blks)
  end. *)
  
Definition gstate_wf (gst: gstate) :=
  forall b, List.In b (local_blks gst) -> Mem.valid_block (gm gst) b /\
  forall mc b ofs res,   (** we only test the shared (i.e. not local) memory regions *)
    (mtest gst) mc (gm gst) b ofs = res ->
      Mem.valid_pointer (gm gst) b ofs = true /\ ~(List.In b (local_blks gst)).
 
(*
Definition update_gmem (gst: gstate) (m: mem): gstate :=
  mkgstate m (grs gst) ()
{|
  gm := m;
  grs := grs gst;
  local_blks := local_blks gst;
  mtest := mtest gst;
  local_blks_wf := local_blks_wf gst;
  mtest_wf := mtest_wf gst;
|}
. *)

Inductive eBPFThread :=
  | eTH: block -> code -> eBPFThread.

  (*
Record eBPFThread := {
  efd: block; (**r eBPF id *)
  eprog: code; (**r eBPF program *)
  eregs: regset; (**r eBPF registers *)
}.*)


Definition atomic64_fun (aty: atomic_type) :=
  match aty with
  | AtomicADD => Val.addl
  | AtomicOR => Val.orl
  | AtomicXOR => Val.xorl
  | AtomicAND => Val.andl
  end.



Inductive gstep (ths: list eBPFThread): gstate -> etrace -> gstate -> Prop :=
  | exec_gstep_thread_local: forall b c rs ofs gst1 et gst2 rs' m',
    In (eTH b c) ths ->
    rs = (grs gst1) b ->
    rs PC = Vptr b ofs ->
    gstate_wf gst1 ->
    step c (State rs (gm gst1)) et (State rs' m') ->
    gst2 = mkgstate m' (fun blk => if Pos.eqb blk b then rs' else (grs gst1) blk) (local_blks gst1) (mtest gst1) ->
    gstate_wf gst2 ->
      gstep ths gst1 et gst2
  | exec_gstep_atomic: forall b c rs ofs gst1 et gst2 rs' m',
    In (eTH b c) ths ->
    rs = (grs gst1) b ->
    rs PC = Vptr b ofs ->
    gstate_wf gst1 ->

      gstep ths gst1 et gst2. *)

Record eBPFThreads := {
  epools: list eBPFThread;
  epools_disjoint: forall e1 e2,
    In e1 epools -> In e2 epools ->
    efd e1 <> efd e2 -> 
}.



End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 ctx_ptr stk_ptr,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
          # PC  <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
          # R1  <- ctx_ptr
          # R10 <- stk_ptr
          # RA  <- Vnullptr in
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