From Coq Require Import ZArith List String.

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.

From bpf.ebpf Require Import ebpfBinSem.

Import ListNotations.

Parameter force_eval : forall {A B : Type}, A -> B -> B.
Definition debug_fail_common (str : string) : bool := false.
Definition debug_fail_step (pc: Ptrofs.int) (r0 r1 r2 r10: val) : bool := false.
Definition debug_fail_stuck (pc: Ptrofs.int) (r0 r1 r2 r10: val) : bool := false.
Definition debug_fail_final (pc: Ptrofs.int) (r0 r1 r2 r10: val) : bool := false.
Definition debug_fail_decode (pc: Ptrofs.int) (raw_insn: int64) : bool := false.
Definition debug_fail_decode_oob (pc: Ptrofs.int) : bool := false.

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

Fixpoint bpf_interpreter (fuel: nat) (bpf_prog: ebpf_prog) (st: outcome) (addr_map: list addr_region): outcome :=
  match fuel with
  | O => Stuck (* assume we have enough fuel *)
  | S k =>
    match st with
    | Stuck => Stuck
    | Next rs stk code_id tail_call_cnt m =>
      match rs PC with
      | Vptr b ofs =>
        match find_code code_id bpf_prog with
        | None => Stuck
        | Some c =>
          match find_instr (Ptrofs.unsigned ofs) c with
          | None => Stuck
          | Some i => bpf_interpreter k bpf_prog (exec_instr bpf_prog i rs stk code_id tail_call_cnt m addr_map) addr_map
          end
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
    match List.nth_error h 0%nat with
    | None => false
    | Some v => is_abstract_value_concrete_eq (rs R0) v addr_map
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
  | RAX => 11
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
  compare_trace_at_pc_aux RAX rs trace addr_map.

Fixpoint bpf_interpreter_trace_check (fuel: nat) (addr_map: list addr_region) (init_sp: int64)  
  (bpf_prog: ebpf_prog) (trace: list (list int64)) (st: outcome): bool :=
  match fuel with
  | O => false (* assume we have fenouagh fuell *)
  | S k =>
    match st with
    | Stuck => false
    | Next rs stk code_id tail_call_cnt m =>
      match rs PC with
      | Vptr b ofs =>
        match find_code code_id bpf_prog with
        | None => false
        | Some c =>
          match find_instr (Ptrofs.unsigned ofs) c with
          | None =>
              let idx := Z.to_nat (Ptrofs.unsigned ofs) in 
              match nth_error c idx with
              | Some raw_insn => debug_fail_decode ofs raw_insn
              | None => debug_fail_decode_oob ofs
              end
          | Some ins =>
            match ins with
            | Pcall CallByStaticID i
            | Pcall CallByBTF i =>
            (** simulating external functions *)
              match trace with
              | [] => false
              | h :: t =>
                match t with
                | [] => false
                | next_h :: next_t =>
                  (* Here we get R0 from next state *)
                  match List.nth_error next_h 0%nat with
                  | None => false
                  | Some r0 =>
                  (** TODO: we assume the return value is Vlong, but it is possible to be a pointer *)
                    bpf_interpreter_trace_check k addr_map init_sp bpf_prog t
                      (Next (nextinstr (rs#R0 <- (Vlong r0))) stk code_id tail_call_cnt m)
                  end
                end
              end
            | _ =>
              if is_final_state ins rs addr_map init_sp then
                if compare_final_state rs trace addr_map then true
                  else debug_fail_final ofs (rs R0) (rs R1) (rs R2) (rs R10)
              else
                match trace with
                | [] => debug_fail_common "Trace ended before program finished"
                | h :: t => 
                  if compare_trace_at_pc rs h addr_map then
                    let next_st := exec_instr bpf_prog ins rs stk code_id tail_call_cnt m addr_map in
                    match next_st with
                    | Stuck => 
                      debug_fail_stuck ofs (rs R0) (rs R1) (rs R2) (rs R10)
                    | _ => 
                      bpf_interpreter_trace_check k addr_map init_sp bpf_prog t next_st
                    end
                  else
                    debug_fail_step ofs (rs R0) (rs R1) (rs R2) (rs R10)
                end
            end
          end
        end
      | _ => false
      end
    end
  end.

Definition create_initial_state (ctx stk pc: block): regset :=
  (Pregmap.init (Vlong Int64.zero))
  (* (Pregmap.init Vundef) *)
    # PC <- (Vptr pc Ptrofs.zero)
    # R10 <- (Vptr stk (Ptrofs.repr bpf_stack_size))
    (* # R10 <- (Vptr stk Ptrofs.zero) *)
    # R1 <- (Vptr ctx Ptrofs.zero)
    (* # BP  <- Vnullptr *)
.

Fixpoint create_jump_table (jmp_blk: block) (ofs: Z) (jmp_table: list (int64 * code)) (addr_map: list addr_region) (m: mem): (list addr_region) * mem :=
  match jmp_table with
  | [] => (addr_map, m)
  | h1 :: tl =>
    let (base, h) := h1 in
  (* we don't need to store the bytecode into memory as we directly access bpf_prog *)
    let (m1, pc_blk1) := Mem.alloc m 0 (Z.of_nat (8*(List.length h))) in
    let m2 :=
      match Mem.storev Mint64 m1 (Vptr jmp_blk (Ptrofs.repr ofs)) (Vptr pc_blk1 Ptrofs.zero) with
      | None => (**should be impossible *) m1
      | Some m' => m'
      end
    in
    let addr_map' := {| 
      base_blk := pc_blk1;
      size_blk := Z.of_nat (8*(List.length h));
      base_addr := base
    |} :: addr_map in
      create_jump_table jmp_blk (ofs+8) tl addr_map' m2
  end.

Fixpoint create_bpf_maps (bpf_maps: list int64) (addr_map: list addr_region) (m: mem): (list addr_region) * mem :=
  match bpf_maps with
  | [] => (addr_map, m)
  | h :: tl =>
    let (m', map_blk1) := Mem.alloc m 0%Z 100%Z in (* for simpilification, assuming the size is 100 *)
    let addr_map' := {| 
      base_blk := map_blk1;
      size_blk := 100%Z;
      base_addr := h
    |} :: addr_map in
      create_bpf_maps tl addr_map' m'
  end.

Fixpoint create_addr_map_sp (stk_blk: block) (sp_list: list int64) (addr_map: list addr_region) (m: mem): (list addr_region) * mem :=
  match sp_list with
  | [] => (addr_map, m)
  | [h] =>
    let addr_map' := {| 
      base_blk := stk_blk;
      size_blk := bpf_stack_size;
      base_addr := Int64.sub h (Int64.repr bpf_stack_size)
    |} :: addr_map in
      (addr_map', m)
  | h :: tl =>
    (** because the begin of semantics_validation_aux has allocated the `stk_blk`, so here we first adding the addr_map, then allocate the next one *)
    let addr_map' := {| 
      base_blk := stk_blk;
      size_blk := bpf_stack_size;
      base_addr := Int64.sub h (Int64.repr bpf_stack_size)
    |} :: addr_map in

    let (m', stk_blk') := Mem.alloc m 0%Z bpf_stack_size in
      create_addr_map_sp stk_blk' tl addr_map' m'
  end.

Definition init_registers (ctx_list: list int64) (rs: regset): regset :=
  match ctx_list with
  | [] => rs
  | r2 :: tl2 =>
    match tl2 with
    | [] => rs
    | r3 :: tl3 =>
      match tl3 with
      | [] => rs
      | r4 :: tl4 =>
        match tl4 with
        | [] => rs
        | r5 :: _ => rs # R2 <- (Vlong r2) 
                        # R3 <- (Vlong r3) 
                        # R4 <- (Vlong r4) 
                        # R5 <- (Vlong r5)
        end
      end
    end
  end. 

Definition semantics_validation_aux (bpf_prog: list int64) (jmp_table: list (int64 * code)) (jmp_table_max: nat) (bpf_maps: list int64) (trace: list (list int64)) (ctx_base : int64) (sp_list: list int64) (ctx_list: list int64): bool :=
  (** assume some information, only for testing *)
  let fuel := 1000 %nat in (* fixed fuel *)
  let ctx_size := 1000 %Z in (* fixed context memort size *)

  (** initial_mem *)
  let m0 := Mem.empty in
  (* we don't need to store the bytecode into memory as we directly access bpf_prog *)
  let (m1, pc_blk) := Mem.alloc m0 0 (Z.of_nat (8*(List.length bpf_prog))) in
  let (m2, ctx_blk) := Mem.alloc m1 0 ctx_size in
  let (m3, stk_blk) := Mem.alloc m2 0 bpf_stack_size in
  (*
    jmp_blk points to the jump_table used by tail_call functions: where
    - [i:i+7] stores a point to the jump_table[i]
  *)
  let (m4, jmp_blk) := Mem.alloc m3 0 (Z.of_nat (8*(List.length jmp_table))) in

  (** addr_map: *)
  let addr_map := [
    {| 
      base_blk := pc_blk;
      size_blk := Z.of_nat (8*(List.length bpf_prog));
      base_addr := Int64.zero  (** TODO we assume pc address is 0 here *) 
    |};
    {| 
      base_blk := ctx_blk;
      size_blk := ctx_size;
      base_addr := ctx_base
    |} ] in
  let (addr_map5, m5) := create_jump_table jmp_blk 0%Z jmp_table addr_map m4 in
  let (addr_map6, m6) := create_bpf_maps (bpf_maps: list int64) addr_map5 m5 in

  let (addr_map', m') := create_addr_map_sp stk_blk sp_list addr_map6 m6 in
  let r10_base := match sp_list with | [] => (** should be impossible *) Int64.zero | h :: tl => h end in

  (** initial_regs *)
  let rs := create_initial_state ctx_blk stk_blk pc_blk in
  let rs1 := init_registers ctx_list rs in
  let init_st := (Next rs1 [] None 0%nat m') in (** None represents to execute the main_code *)

    bpf_interpreter_trace_check fuel addr_map' r10_base 
          {|  main_code := bpf_prog;
              jump_table := List.map (fun x => snd x) jmp_table;
              max_entries := jmp_table_max |}
          trace init_st.

(** trace stores [R0-R10] values executed by core.c of Linux eBPF VM *)
Definition semantics_validation (bpf_prog: code) (jmp_table: list (int64 * code)) (jmp_table_max: nat) (bpf_maps: list int64) (trace: list (list int64)) (sp_list: list int64) (ctx_list: list int64): bool :=
  match trace with
  | [] => false
  | h :: t =>
    match ctx_list with
    | [] => false
    | ctx_base :: tl =>
        semantics_validation_aux bpf_prog jmp_table jmp_table_max
          bpf_maps trace ctx_base sp_list tl
    end
  end.