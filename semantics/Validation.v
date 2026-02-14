From Coq Require Import ZArith List.

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.

From bpf.ebpf Require Import ebpfBinSem.

Import ListNotations.

Definition get_sub_insn (ins: int64) (from size: nat): int64 :=
  Int64.unsigned_bitfield_extract (Z.of_nat from) (Z.of_nat size) ins.

Definition decode_insn (opcode : byte) (dst_reg src_reg : ireg) (off : Ptrofs.int) (imm : int) : option instruction :=
  match (Byte.unsigned opcode) with
  (* Palu *)
  | 0x04 => Some (Palu ADD W32 dst_reg (inr imm))
  | 0x07 => Some (Palu ADD W64 dst_reg (inr imm))
  | 0x0c => Some (Palu ADD W32 dst_reg (inl src_reg))
  | 0x0f => Some (Palu ADD W64 dst_reg (inl src_reg))
  | 0x14 => Some (Palu SUB W32 dst_reg (inr imm))
  | 0x17 => Some (Palu SUB W64 dst_reg (inr imm))
  | 0x1c => Some (Palu SUB W32 dst_reg (inl src_reg))
  | 0x1f => Some (Palu SUB W64 dst_reg (inl src_reg))
  | 0x24 => Some (Palu MUL W32 dst_reg (inr imm))
  | 0x27 => Some (Palu MUL W64 dst_reg (inr imm))
  | 0x2c => Some (Palu MUL W32 dst_reg (inl src_reg))
  | 0x2f => Some (Palu MUL W64 dst_reg (inl src_reg))
  | 0x34 =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu DIV W32 dst_reg (inr imm))
    | 1 => Some (Palu SDIV W32 dst_reg (inr imm))
    | _ => None
    end
  | 0x37 =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu DIV W64 dst_reg (inr imm))
    | 1 => Some (Palu SDIV W64 dst_reg (inr imm))
    | _ => None
    end
  | 0x3c =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu DIV W32 dst_reg (inl src_reg))
    | 1 => Some (Palu SDIV W32 dst_reg (inl src_reg))
    | _ => None
    end
  | 0x3f =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu DIV W64 dst_reg (inl src_reg))
    | 1 => Some (Palu SDIV W64 dst_reg (inl src_reg))
    | _ => None
    end
  | 0x44 => Some (Palu OR W32 dst_reg (inr imm))
  | 0x47 => Some (Palu OR W64 dst_reg (inr imm))
  | 0x4c => Some (Palu OR W32 dst_reg (inl src_reg))
  | 0x4f => Some (Palu OR W64 dst_reg (inl src_reg))
  | 0x54 => Some (Palu AND W32 dst_reg (inr imm))
  | 0x57 => Some (Palu AND W64 dst_reg (inr imm))
  | 0x5c => Some (Palu AND W32 dst_reg (inl src_reg))
  | 0x5f => Some (Palu AND W64 dst_reg (inl src_reg))
  | 0x64 => Some (Palu LSH W32 dst_reg (inr imm))
  | 0x67 => Some (Palu LSH W64 dst_reg (inr imm))
  | 0x6c => Some (Palu LSH W32 dst_reg (inl src_reg))
  | 0x6f => Some (Palu LSH W64 dst_reg (inl src_reg))
  | 0x74 => Some (Palu RSH W32 dst_reg (inr imm))
  | 0x77 => Some (Palu RSH W64 dst_reg (inr imm))
  | 0x7c => Some (Palu RSH W32 dst_reg (inl src_reg))
  | 0x7f => Some (Palu RSH W64 dst_reg (inl src_reg))
  | 0x84 =>
    if (ireg_eqb src_reg R0) then
      Some (Palu NEG W32 dst_reg (inr imm))
    else
      None
  | 0x87 =>
    if (ireg_eqb src_reg R0) then
      Some (Palu NEG W64 dst_reg (inr imm))
    else
      None
  | 0x94 =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu MOD W32 dst_reg (inr imm))
    | 1 => Some (Palu SMOD W32 dst_reg (inr imm))
    | _ => None
    end
  | 0x97 =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu MOD W64 dst_reg (inr imm))
    | 1 => Some (Palu SMOD W64 dst_reg (inr imm))
    | _ => None
    end
  | 0x9c =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu MOD W32 dst_reg (inl src_reg))
    | 1 => Some (Palu SMOD W32 dst_reg (inl src_reg))
    | _ => None
    end
  | 0x9f =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu MOD W64 dst_reg (inl src_reg))
    | 1 => Some (Palu SMOD W64 dst_reg (inl src_reg))
    | _ => None
    end
  | 0xa4 => Some (Palu XOR W32 dst_reg (inr imm))
  | 0xa7 => Some (Palu XOR W64 dst_reg (inr imm))
  | 0xac => Some (Palu XOR W32 dst_reg (inl src_reg))
  | 0xaf => Some (Palu XOR W64 dst_reg (inl src_reg))
  | 0xb4 => Some (Palu MOV W32 dst_reg (inr imm))
  | 0xb7 => Some (Palu MOV W64 dst_reg (inr imm))
  | 0xbc =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu MOV W32 dst_reg (inl src_reg))
    | 8 => Some (Palu (MOVSX SZ8) W32 dst_reg (inl src_reg))
    | 16 => Some (Palu (MOVSX SZ16) W32 dst_reg (inl src_reg))
    | _ => None
    end
  | 0xbf =>
    match (Ptrofs.signed off) with
    | 0 => Some (Palu MOV W64 dst_reg (inl src_reg))
    | 8 => Some (Palu (MOVSX SZ8) W64 dst_reg (inl src_reg))
    | 16 => Some (Palu (MOVSX SZ16) W64 dst_reg (inl src_reg))
    | 32 => Some (Palu (MOVSX SZ32) W64 dst_reg (inl src_reg))
    | _ => None
    end
  | 0xc4 => Some (Palu ARSH W32 dst_reg (inr imm))
  | 0xc7 => Some (Palu ARSH W64 dst_reg (inr imm))
  | 0xcc => Some (Palu ARSH W32 dst_reg (inl src_reg))
  | 0xcf => Some (Palu ARSH W64 dst_reg (inl src_reg))
  | 0xd4 =>
    if (ireg_eqb src_reg R0) then
      match (Int.signed imm) with
      | 0x10 => Some (Palu (END LE32 S16) W32 dst_reg (inr imm))
      | 0x20 => Some (Palu (END LE32 S32) W64 dst_reg (inr imm))
      | 0x40 => Some (Palu (END LE32 S64) W32 dst_reg (inr imm))
      | _ => None
      end
    else
      None
  | 0xd7 =>
    if (ireg_eqb src_reg R0) then
      match (Int.signed imm) with
      | 0x10 => Some (Palu (END LE64 S16) W32 dst_reg (inr imm))
      | 0x20 => Some (Palu (END LE64 S32) W64 dst_reg (inr imm))
      | 0x40 => Some (Palu (END LE64 S64) W32 dst_reg (inr imm))
      | _ => None
      end
    else
      None
  | 0xdc =>
    if (ireg_eqb src_reg R0) then
      match (Int.signed imm) with
      | 0x10 => Some (Palu (END BE32 S16) W32 dst_reg (inr imm))
      | 0x20 => Some (Palu (END BE32 S32) W64 dst_reg (inr imm))
      | 0x40 => Some (Palu (END BE32 S64) W32 dst_reg (inr imm))
      | _ => None
      end
    else
      None
  (* Pjmp32 + Pjmp64 *)
  | 0x05 =>
    if (ireg_eqb src_reg R0 && Z.eqb (Int.signed imm) 0) then
      Some (Pjmp64 off)
    else
      None
  | 0x06 =>
    if (ireg_eqb src_reg R0 && Z.eqb (Ptrofs.signed off) 0) then
      Some (Pjmp32 imm)
    else
      None
  (* Pjmpcmp *)
  | 0x15 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp EQ W64 dst_reg (inr imm) off)
    else
      None
  | 0x16 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp EQ W32 dst_reg (inr imm) off)
    else
      None
  | 0x1d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp EQ W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x1e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp EQ W32 dst_reg (inl src_reg) off)
    else
      None
  | 0x25 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GT Unsigned) W64 dst_reg (inr imm) off)
    else
      None
  | 0x26 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GT Unsigned) W32 dst_reg (inr imm) off)
    else
      None
  | 0x2d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GT Unsigned) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x2e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GT Unsigned) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0x35 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GE Unsigned) W64 dst_reg (inr imm) off)
    else
      None
  | 0x36 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GE Unsigned) W32 dst_reg (inr imm) off)
    else
      None
  | 0x3d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GE Unsigned) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x3e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GE Unsigned) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0x45 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp SET W64 dst_reg (inr imm) off)
    else
      None
  | 0x46 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp SET W32 dst_reg (inr imm) off)
    else
      None
  | 0x4d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp SET W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x4e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp SET W32 dst_reg (inl src_reg) off)
    else
      None
  | 0x55 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp NE W64 dst_reg (inr imm) off)
    else
      None
  | 0x56 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp NE W32 dst_reg (inr imm) off)
    else
      None
  | 0x5d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp NE W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x5e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp NE W32 dst_reg (inl src_reg) off)
    else
      None
  | 0x65 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GT Signed) W64 dst_reg (inr imm) off)
    else
      None
  | 0x66 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GT Signed) W32 dst_reg (inr imm) off)
    else
      None
  | 0x6d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GT Signed) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x6e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GT Signed) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0x75 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GE Signed) W64 dst_reg (inr imm) off)
    else
      None
  | 0x76 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (GE Signed) W32 dst_reg (inr imm) off)
    else
      None
  | 0x7d =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GE Signed) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0x7e =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (GE Signed) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0xa5 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LT Unsigned) W64 dst_reg (inr imm) off)
    else
      None
  | 0xa6 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LT Unsigned) W32 dst_reg (inr imm) off)
    else
      None
  | 0xad =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LT Unsigned) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0xae =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LT Unsigned) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0xb5 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LE Unsigned) W64 dst_reg (inr imm) off)
    else
      None
  | 0xb6 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LE Unsigned) W32 dst_reg (inr imm) off)
    else
      None
  | 0xbd =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LE Unsigned) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0xbe =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LE Unsigned) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0xc5 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LT Signed) W64 dst_reg (inr imm) off)
    else
      None
  | 0xc6 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LT Signed) W32 dst_reg (inr imm) off)
    else
      None
  | 0xcd =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LT Signed) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0xce =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LT Signed) W32 dst_reg (inl src_reg) off)
    else
      None
  | 0xd5 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LE Signed) W64 dst_reg (inr imm) off)
    else
      None
  | 0xd6 =>
    if (ireg_eqb src_reg R0) then
      Some (Pjmpcmp (LE Signed) W32 dst_reg (inr imm) off)
    else
      None
  | 0xdd =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LE Signed) W64 dst_reg (inl src_reg) off)
    else
      None
  | 0xde =>
    if Z.eqb (Int.signed imm) 0 then
      Some (Pjmpcmp (LE Signed) W32 dst_reg (inl src_reg) off)
    else
      None
  (* Pret *)
  | 0x95 =>
    if (ireg_eqb src_reg R0 && Z.eqb (Int.signed imm) 0 && Z.eqb (Ptrofs.signed off) 0) then
      Some Pret
    else
      None
  (* Pcall *)
  | 0x85 =>
    if (Z.eqb (Ptrofs.signed off) 0) then
      match src_reg with
      | R1 => Some (Pcall CallInternal imm)
      | _ => None
      end
    else
      None
  (* Pload *)
  | 0x61 =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pload Word dst_reg src_reg off)
    else
      None
  | 0x69 =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pload HalfWord dst_reg src_reg off)
    else
      None
  | 0x71 =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pload Byte dst_reg src_reg off)
    else
      None
  | 0x79 =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pload DBWord dst_reg src_reg off)
    else
      None
  (* Pstore *)
  | 0x62 =>
    if (ireg_eqb src_reg R0) then
      Some (Pstore Word dst_reg (inr imm) off)
    else
      None
  | 0x63 =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pstore Word dst_reg (inl src_reg) off)
    else
      None
  | 0x6a =>
    if (ireg_eqb src_reg R0) then
      Some (Pstore HalfWord dst_reg (inr imm) off)
    else
      None
  | 0x6b =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pstore HalfWord dst_reg (inl src_reg) off)
    else
      None
  | 0x72 =>
    if (ireg_eqb src_reg R0) then
      Some (Pstore Byte dst_reg (inr imm) off)
    else
      None
  | 0x73 =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pstore Byte dst_reg (inl src_reg) off)
    else
      None
  | 0x7a =>
    if (ireg_eqb src_reg R0) then
      Some (Pstore DBWord dst_reg (inr imm) off)
    else
      None
  | 0x7b =>
    if (Z.eqb (Int.signed imm) 0) then
      Some (Pstore DBWord dst_reg (inl src_reg) off)
    else
      None
  | _ => None
  end.

Definition decode_lddw_insn (dst_reg src_reg : ireg) (imm next_imm : int) : option instruction :=
  match src_reg with
  | R0 => Some (Plddw dst_reg imm next_imm)
  (* TODO : R1~R6 *)
  | _ => None
  end.

Definition Z_to_ireg (i : Z) : option ireg :=
  match i with
  | 0 => Some R0 | 1 => Some R1 | 2 => Some R2
  | 3 => Some R3 | 4 => Some R4 | 5 => Some R5
  | 6 => Some R6 | 7 => Some R7 | 8 => Some R8
  | 9 => Some R9 | 10 => Some R10 | _ => None
  end.

Definition find_instr (pc : Z) (bpf_prog : code) : option instruction :=
  match (nth_error bpf_prog (Z.to_nat pc)) with
  | None => None
  | Some data =>
    let opcode := Byte.repr (Int64.unsigned (get_sub_insn data 0 8)) in
    let dst_reg := Z_to_ireg (Int64.unsigned (get_sub_insn data 8 4)) in
    let src_reg := Z_to_ireg (Int64.unsigned (get_sub_insn data 12 4)) in
    let off := Ptrofs.repr (Int64.signed (get_sub_insn data 16 16)) in
    let imm := Int.repr (Int64.signed (get_sub_insn data 32 32)) in
    match dst_reg, src_reg with
    | Some dst_reg, Some src_reg =>
      if Z.eqb (Byte.unsigned opcode) 0x18 then
        (* LDDW insn *)
        match (nth_error bpf_prog (Z.to_nat (pc + 1))) with
        | None => None
        | Some data2 =>
          let reserved := Int64.signed (get_sub_insn data2 0 32) in
          let next_imm := Int.repr (Int64.signed (get_sub_insn data2 32 32)) in
            if (Z.eqb reserved 0) then
              decode_lddw_insn dst_reg src_reg imm next_imm
            else
              None
        end
      else
        (* common insn *)
        decode_insn opcode dst_reg src_reg off imm
    | _, _ => None
    end
  end.

Fixpoint bpf_interpreter (fuel: nat) (bpf_prog: list int64) (st: outcome) (l_ptr: list int64)  (addr_map: list addr_region): outcome :=
  match fuel with
  | O => Stuck (* assume we have enough fuel *)
  | S k =>
    match st with
    | Stuck => Stuck
    | Next rs stk m =>
      match rs PC with
      | Vptr b ofs =>
        match find_instr (Ptrofs.unsigned ofs) bpf_prog with
        | None => Stuck
        | Some i => bpf_interpreter k bpf_prog (exec_instr i rs stk m l_ptr addr_map) l_ptr addr_map
        end
      | _ => Stuck
      end
    end
  end.

Fixpoint find_concrete_address (b: block) (addr_map: list addr_region): option int64 :=
  match addr_map with
  | [] => None
  | h :: t =>
    if Pos.eqb (base_blk h) b then
      Some (base_addr h)
    else
      find_concrete_address b t
  end.

Definition cast_address_abs_to_concrete (addr: val) (addr_map: list addr_region): option int64 :=
  match addr with
  | Vptr b ofs =>
    match find_concrete_address b addr_map with
    | None => None
    | Some v => Some (Int64.add v (Ptrofs.to_int64 ofs))
    end
  | _ => None
  end.

Definition is_final_state (ins: instruction) (rs: regset) (addr_map: list addr_region) (init_sp: int64): bool :=
  match ins with
  | Pret =>
    match (rs R10) with
    | Vptr b ofs =>
      match cast_address_abs_to_concrete (Vptr b ofs) addr_map with
      | None => false
      | Some i => Int64.eq init_sp i
      end
    | _ => false
    end
  | _ => false
  end.
(**r
- when av is Vlong, just compare two int64
- when av is ptr, first cast ptr to int64, then compare two int64
*)
Definition is_abstract_value_concrete_eq (av: val) (cv: int64) (addr_map: list addr_region): bool :=
  match av with
  | Vlong i => Int64.eq cv i
  | Vptr b ofs =>
    match cast_address_abs_to_concrete (Vptr b ofs) addr_map with
    | None => false
    | Some i => Int64.eq cv i
    end
  | Vundef => true
  (** the Coq model will set some register value to Vundef while the Linux eBPF C version will give arbitrary value: for exmaple, 
  - the initial state of Coq version set most register to Vundef, while the C version will be zero (?) 
  - And the internal call produce finishes, r1-r5 are Vundef at Coq, but we don't know the value of C version (?may the old register value?)  *)
  | _ => false
  end.

Definition compare_final_state (rs: regset) (trace: list (list int64)) (addr_map: list addr_region): bool :=
  match trace with
  | [h] =>
    match List.nth_error h 1%nat with
    | None => false
    | Some v => is_abstract_value_concrete_eq (rs R1) v addr_map
    end
  | _ => false
  end.

Definition nat_of_ireg (r: ireg): nat :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Definition compare_trace_at_pc_aux (r: ireg) (rs: regset) (trace: list int64) (addr_map: list addr_region): bool :=
  match List.nth_error trace (nat_of_ireg r) with
  | None => false
  | Some cv => is_abstract_value_concrete_eq (rs r) cv addr_map
  end.

Definition compare_trace_at_pc (rs: regset) (trace: list int64) (addr_map: list addr_region): bool :=
  compare_trace_at_pc_aux R0 rs trace addr_map &&
  compare_trace_at_pc_aux R1 rs trace addr_map &&
  compare_trace_at_pc_aux R2 rs trace addr_map &&
  compare_trace_at_pc_aux R3 rs trace addr_map &&
  compare_trace_at_pc_aux R4 rs trace addr_map &&
  compare_trace_at_pc_aux R5 rs trace addr_map &&
  compare_trace_at_pc_aux R6 rs trace addr_map &&
  compare_trace_at_pc_aux R7 rs trace addr_map &&
  compare_trace_at_pc_aux R8 rs trace addr_map &&
  compare_trace_at_pc_aux R9 rs trace addr_map &&
  compare_trace_at_pc_aux R10 rs trace addr_map.

Fixpoint bpf_interpreter_trace_check (fuel: nat) (l_ptr: list int64)  (addr_map: list addr_region) (init_sp: int64)  
  (bpf_prog: list int64) (trace: list (list int64)) (st: outcome): bool :=
  match fuel with
  | O => false (* assume we have fenouagh fuell *)
  | S k =>
    match st with
    | Stuck => false
    | Next rs stk m =>
      match rs PC with
      | Vptr b ofs =>
        match find_instr (Ptrofs.unsigned ofs) bpf_prog with
        | None => false
        | Some ins =>
          match ins with
          | Pcall CallByStaticID i
          | Pcall CallByBTF i =>
          (** simulating external functions *)
            match trace with
            | [] => false
            | h :: t =>
              match List.nth_error h 0%nat with
              | None => false
              | Some r0 =>
              (** TODO: we assume the return value is Vlong, but it is possible to be a pointer *)
                bpf_interpreter_trace_check k l_ptr addr_map init_sp bpf_prog trace
                  (Next (nextinstr (rs#R0 <- (Vlong r0))) stk m)
              end
            end
          | _ =>
            if is_final_state ins rs addr_map init_sp then
              compare_final_state rs trace addr_map
            else
              match trace with
              | [] => false
              | h :: t => 
                if compare_trace_at_pc rs h addr_map then
                  false
                else
                  bpf_interpreter_trace_check k l_ptr addr_map init_sp bpf_prog t (exec_instr ins rs stk m l_ptr addr_map)
              end
          end
        end
      | _ => false
      end
    end
  end.

Definition create_initial_state (ctx stk pc: block): regset :=
  (Pregmap.init Vundef)
    # PC <- (Vptr pc Ptrofs.zero)
    # R10 <- (Vptr stk Ptrofs.zero)
    # R1 <- (Vptr ctx Ptrofs.zero)
    (* # BP  <- Vnullptr *)
.

Definition semantics_validation_aux (bpf_prog: list int64) (trace: list (list int64)) (l_ptr: list int64) (ctx_base r10_base : int64): bool :=
  (** assume some information, only for testing *)
  let fuel := 1000 %nat in (* fixed fuel *)
  let ctx_size := 1000 %Z in (* fixed context memort size *)

  (** initial_mem *)
  let m0 := Mem.empty in
  let (m1, pc_blk) := Mem.alloc m0 0 (Z.of_nat (List.length bpf_prog)) in
  let (m2, ctx_blk) := Mem.alloc m1 0 ctx_size in
  let (m3, stk_blk) := Mem.alloc m2 0 bpf_stack_size in

  (** addr_map: *)
  let addr_map := [
    {| 
      base_blk := pc_blk;
      size_blk := Z.of_nat (List.length bpf_prog);
      base_addr := Int64.zero  (** TODO we assume pc address is 0 here *) 
    |};
    {| 
      base_blk := ctx_blk;
      size_blk := 30;  (** TODO we assume size_blk is 30 here *) 
      base_addr := ctx_base
    |};
    {| 
      base_blk := stk_blk;
      size_blk := bpf_stack_size;
      base_addr := r10_base
    |} ] in

  (** initial_regs *)
  let rs := create_initial_state ctx_blk stk_blk pc_blk in

    bpf_interpreter_trace_check fuel l_ptr addr_map r10_base bpf_prog trace (Next rs [] m3).

(** trace stores [R0-R10] values executed by core.c of Linux eBPF VM *)
Definition semantics_validation (bpf_prog: list int64) (trace: list (list int64)) (l_ptr: list int64): bool :=
  match trace with
  | [] => false
  | h :: t =>
    match List.nth_error h 1%nat with
    | None => false
    | Some ctx_base =>
      match List.nth_error h 10%nat with
      | None => false
      | Some r10_base =>
        semantics_validation_aux bpf_prog trace l_ptr ctx_base r10_base
      end
    end
  end.