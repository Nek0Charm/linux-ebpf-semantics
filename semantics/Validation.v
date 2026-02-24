From Coq Require Import ZArith List.

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.

From bpf.ebpf Require Import ebpfBinSem.

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

    else if Z.eqb code 0x8 && is_jmp64 && src_is_imm then (* CALL *)
      if check_off_0 then
        match src_reg with
        | R1 => Some (Pcall CallInternal imm)
        | _ => None
        end
      else None
       
    else if Z.eqb code 0x9 && is_jmp64 && src_is_reg then (* EXIT *)
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

  (* ==================== MEMORY (LDX, ST, STX) ==================== *)
  else if is_ldx || is_st || is_stx then
    if Z.eqb (Z.shiftr op_val 5) 0x3 then (* Mode = MEM (0x60) *)
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
    else None
  else
    None.

Definition decode_lddw_insn (dst_reg src_reg : ireg) (imm next_imm : int) : option instruction :=
  match src_reg with
  | R0 => Some (Plddw PSEUDO_Constant dst_reg imm next_imm)
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
                  bpf_interpreter_trace_check k l_ptr addr_map init_sp bpf_prog t (exec_instr ins rs stk m l_ptr addr_map)
                else
                  false
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
      size_blk := ctx_size;
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