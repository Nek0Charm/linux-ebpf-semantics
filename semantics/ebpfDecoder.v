From Coq Require Import ZArith List String.

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.

From bpf.ebpf Require Import ebpfSyntax ebpfState.

Import ListNotations.

Definition get_sub_insn (ins: int64) (from size: nat): int64 :=
  Int64.unsigned_bitfield_extract (Z.of_nat from) (Z.of_nat size) ins.

Module BPF_CLASS.
  Definition LD    : Z := 0x0.
  Definition LDX   : Z := 0x1.
  Definition ST    : Z := 0x2.
  Definition STX   : Z := 0x3.
  Definition ALU32 : Z := 0x4.
  Definition JMP64 : Z := 0x5.
  Definition JMP32 : Z := 0x6.
  Definition ALU64 : Z := 0x7.
End BPF_CLASS.

Module BPF_SRC.
  Definition K : Z := 0x0. (* Immediate *)
  Definition X : Z := 0x1. (* Register *)
End BPF_SRC.

Definition decode_insn (opcode : byte) (dst_reg src_reg : ireg) (off : Ptrofs.int) (imm : int) : option instruction :=
  let op_val := Byte.unsigned opcode in

  let cls    := Z.land op_val 0x07 in
  let src    := Z.land (Z.shiftr op_val 3) 0x01 in
  let code   := Z.shiftr op_val 4 in

  let is_ldx      := Z.eqb cls BPF_CLASS.LDX in
  let is_st       := Z.eqb cls BPF_CLASS.ST in
  let is_stx      := Z.eqb cls BPF_CLASS.STX in
  let is_alu32    := Z.eqb cls BPF_CLASS.ALU32 in
  let is_jmp64    := Z.eqb cls BPF_CLASS.JMP64 in
  let is_jmp32    := Z.eqb cls BPF_CLASS.JMP32 in
  let is_alu64    := Z.eqb cls BPF_CLASS.ALU64 in
  
  let src_is_reg  := Z.eqb src BPF_SRC.X in
  let src_is_imm  := Z.eqb src BPF_SRC.K in

  let check_src_r0 := ireg_eqb src_reg R0 in
  let check_dst_r0 := ireg_eqb dst_reg R0 in
  let check_imm_0  := Z.eqb (Int.signed imm) 0 in
  let check_off_0  := Z.eqb (Ptrofs.signed off) 0 in

  let src_op := if src_is_imm then inr imm else inl src_reg in

  (* ==================== ALU (ALU32 / ALU64) ==================== *)
  if is_alu32 || is_alu64 then
    let width := if is_alu64 then W64 else W32 in
    match code with
    | 0x0 => Some (Palu ADD width dst_reg src_op)       (* ADD *)
    | 0x1 => Some (Palu SUB width dst_reg src_op)       (* SUB *)
    | 0x2 => Some (Palu MUL width dst_reg src_op)       (* MUL *)
    | 0x3 => (* DIV *)
        match Ptrofs.signed off with
        | 0 => Some (Palu DIV width dst_reg src_op)
        | 1 => Some (Palu SDIV width dst_reg src_op)
        | _ => None
        end
    | 0x4 => Some (Palu OR width dst_reg src_op)        (* OR  *)
    | 0x5 => Some (Palu AND width dst_reg src_op)       (* AND *)
    | 0x6 => Some (Palu LSH width dst_reg src_op)       (* LSH *)
    | 0x7 => Some (Palu RSH width dst_reg src_op)       (* RSH *)
    | 0x8 => (* NEG *)
        if check_src_r0 then Some (Palu NEG width dst_reg (inr imm)) else None
    | 0x9 => (* MOD *)
        match Ptrofs.signed off with
        | 0 => Some (Palu MOD width dst_reg src_op)
        | 1 => Some (Palu SMOD width dst_reg src_op)
        | _ => None
        end
    | 0xa => Some (Palu XOR width dst_reg src_op)       (* XOR *)
    | 0xb => (* MOV *)
        if src_is_reg then
           match Ptrofs.signed off with
           | 0x0  => Some (Palu MOV width dst_reg src_op)
           | 0x8  => Some (Palu (MOVSX SZ8) width dst_reg src_op)
           | 0x10 => Some (Palu (MOVSX SZ16) width dst_reg src_op)
           | 0x20 => if is_alu64 then Some (Palu (MOVSX SZ32) W64 dst_reg src_op) else None
           | _  => None
           end
        else Some (Palu MOV width dst_reg src_op)
    | 0xc => Some (Palu ARSH width dst_reg src_op)      (* ARSH *)
    | 0xd => (* END *)
        if check_src_r0 then
          let endian_opt := 
            if is_alu32 then
              if src_is_imm then Some LE32 else Some BE32
            else
              if src_is_imm then Some LE64 else None
          in
          
          match endian_opt with
          | Some e => 
              match Int.signed imm with
              | 0x10 => Some (Palu (END e S16) W32 dst_reg (inr imm))
              | 0x20 => Some (Palu (END e S32) W32 dst_reg (inr imm))
              | 0x40 => Some (Palu (END e S64) W64 dst_reg (inr imm))
              | _ => None
              end
          | None => None
          end
        else None
    | _ => None
    end

  (* ==================== JUMP (JMP64 / JMP32) ==================== *)
  else if is_jmp64 || is_jmp32 then
    if Z.eqb code 0x0 then (* JA *)
      if is_jmp64 then
        if check_src_r0 && check_imm_0 then Some (Pjmp64 off) else None
      else
        if check_src_r0 && check_off_0 then Some (Pjmp32 imm) else None
    else if Z.eqb code 0xf && is_jmp64 then (* JMP_TAIL_CALL *)
      if check_dst_r0 && check_src_r0 && check_off_0 && check_imm_0 then Some Ptail_call else None
    else if Z.eqb code 0x8 && is_jmp64 && src_is_imm then (* CALL *)
      if check_off_0 then
        match src_reg with
        | R0 => Some (Pcall CallByStaticID imm)
        | R1 => Some (Pcall CallInternal imm)
        | R2 => Some (Pcall CallByBTF imm)
        | _ => None
        end
      else None
       
    else if Z.eqb code 0x9 && is_jmp64 && src_is_imm then (* EXIT *)
      if check_src_r0 && check_imm_0 && check_off_0 then Some Pret else None

    else (* Conditional Jumps *)
      let width := if is_jmp64 then W64 else W32 in
      let valid_args := if src_is_imm then check_src_r0 else check_imm_0 in
      
      if valid_args then
        match code with
        | 0x1 => Some (Pjmpcmp EQ width dst_reg src_op off)
        | 0x2 => Some (Pjmpcmp (GT Unsigned) width dst_reg src_op off)
        | 0x3 => Some (Pjmpcmp (GE Unsigned) width dst_reg src_op off)
        | 0x4 => Some (Pjmpcmp SET width dst_reg src_op off)
        | 0x5 => Some (Pjmpcmp NE width dst_reg src_op off)
        | 0x6 => Some (Pjmpcmp (GT Signed) width dst_reg src_op off)
        | 0x7 => Some (Pjmpcmp (GE Signed) width dst_reg src_op off)
        | 0xa => Some (Pjmpcmp (LT Unsigned) width dst_reg src_op off)
        | 0xb => Some (Pjmpcmp (LE Unsigned) width dst_reg src_op off)
        | 0xc => Some (Pjmpcmp (LT Signed) width dst_reg src_op off)
        | 0xd => Some (Pjmpcmp (LE Signed) width dst_reg src_op off)
        | _   => None
        end
      else None

  (* ==================== MEMORY (LDX, LDX_PROBE, LDSX, LDSX_PROBE, ST_NOSPEC, ST, STX) ==================== *)
  else if is_ldx || is_st || is_stx then
    if Z.eqb op_val 0xc2 then 
      if check_imm_0 && check_off_0 && check_src_r0 && check_dst_r0 then Some Pno_spec else None
    else if Z.eqb (Z.shiftr op_val 5) 0x3 then (* Mode = MEM (0x60) *)
      let sz := Z.land (Z.shiftr op_val 3) 0x3 in (* Size bits 3-4 *)
      let mem_sz := match sz with
                    | 0x0 => Some Word
                    | 0x1 => Some HalfWord
                    | 0x2 => Some Byte
                    | 0x3 => Some DBWord
                    | _ => None
                    end in
      match mem_sz with
      | Some sz =>
        if is_ldx then
          if check_imm_0 then Some (Pload sz dst_reg src_reg off) else None
        else if is_st then
          if check_src_r0 then Some (Pstore sz dst_reg (inr imm) off) else None
        else (* is_stx *)
          if check_imm_0 then Some (Pstore sz dst_reg (inl src_reg) off) else None
      | None => None
      end
    else if Z.eqb (Z.shiftr op_val 5) 0x4 then (* Mode = MEM (0x80) *)
      let sz := Z.land (Z.shiftr op_val 3) 0x3 in (* Size bits 3-4 *)
      let mem_sz := match sz with
                    | 0x0 => Some Word
                    | 0x1 => Some HalfWord
                    | 0x2 => Some Byte
                    | _ => None
                    end in
      match mem_sz with
      | Some sz =>
        if is_ldx then
          if check_imm_0 then Some (Ploadsx sz dst_reg src_reg off) else None
        else None
      | None => None
      end
    else if Z.eqb (Z.shiftr op_val 5) 0x1 then (* Mode = MEM (0x20) *)
      let sz := Z.land (Z.shiftr op_val 3) 0x3 in (* Size bits 3-4 *)
      let mem_sz := match sz with
                    | 0x0 => Some Word
                    | 0x1 => Some HalfWord
                    | 0x2 => Some Byte
                    | 0x3 => Some DBWord
                    | _ => None
                    end in
      match mem_sz with
      | Some sz =>
        if is_ldx then
          if check_imm_0 then Some (Pload_probe sz dst_reg src_reg off) else None
        else None
      | None => None
      end
    else if Z.eqb (Z.shiftr op_val 5) 0x2 then (* Mode = MEM (0x40) *)
      let sz := Z.land (Z.shiftr op_val 3) 0x3 in (* Size bits 3-4 *)
      let mem_sz := match sz with
                    | 0x0 => Some Word
                    | 0x1 => Some HalfWord
                    | 0x2 => Some Byte
                    | _ => None
                    end in
      match mem_sz with
      | Some sz =>
        if is_ldx then
          if check_imm_0 then Some (Ploadsx_probe sz dst_reg src_reg off) else None
        else None
      | None => None
      end

    else None
  else
    None.

Definition decode_lddw_insn (dst_reg src_reg : ireg) (imm next_imm : int) : option instruction :=
  match src_reg with
  | R0 => Some (Plddw PSEUDO_Constant dst_reg imm next_imm)
  (* TODO : R1~R6 *)
  | R1 => Some (Plddw PSEUDO_MAP_FD dst_reg imm next_imm)
  | R5 => Some (Plddw PSEUDO_MAP_IDX dst_reg imm next_imm)
  | R2 => Some (Plddw PSEUDO_MAP_VALUE dst_reg imm next_imm)
  | R6 => Some (Plddw PSEUDO_MAP_IDX_VALUE dst_reg imm next_imm)
  | R3 => Some (Plddw PSEUDO_BTF_ID dst_reg imm next_imm)
  | R4 => Some (Plddw PSEUDO_FUNC dst_reg imm next_imm)
  | _ => None
  end.

Definition Z_to_ireg (i : Z) : option ireg :=
  match i with
  | 0 => Some R0 | 1 => Some R1 | 2 => Some R2
  | 3 => Some R3 | 4 => Some R4 | 5 => Some R5
  | 6 => Some R6 | 7 => Some R7 | 8 => Some R8
  | 9 => Some R9 | 10 => Some R10 | 11 => Some RAX
  | _ => None
  end.

Definition find_instr (pc : Z) (bpf_prog : code) : option instruction :=
  match (nth_error bpf_prog (Z.to_nat pc)) with
  | None => None
  | Some data =>
    let opcode := Byte.repr (Int64.unsigned (get_sub_insn data 0 8)) in
    let dst_reg := Z_to_ireg (Int64.unsigned (get_sub_insn data 8 4)) in
    let src_reg := Z_to_ireg (Int64.unsigned (get_sub_insn data 12 4)) in
    let off := Ptrofs.repr (Int64.signed (Int64.sign_ext 16 (get_sub_insn data 16 16))) in
    let imm := Int.repr (Int64.signed (Int64.sign_ext 32 (get_sub_insn data 32 32))) in
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