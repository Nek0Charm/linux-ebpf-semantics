From Coq Require Import ZArith List String.

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.

From bpf.ebpf Require Import ebpfSyntax ebpfState ebpfDecoder ebpfBinSem.

Import ListNotations.

Parameter force_eval : forall {A B : Type}, A -> B -> B.

Definition debug_fail_common (str : string) : bool := false.

(* err_code: 0=Step Mismatch, 1=Stuck, 2=Final Mismatch *)
Definition debug_fail_exec (err_code: nat) 
                           (pc: Ptrofs.int)
                           (ins: instruction)
                           (rs_before rs_after: regset)
                           (expected_trace: list int64)
                           (addr_map: list addr_region) : bool := false.

Definition debug_fail_decode (pc: Ptrofs.int) (raw_insn: int64) : bool := false.
Definition debug_fail_decode_oob (pc: Ptrofs.int) : bool := false.

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

(*
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
  end. *)
Definition is_final_state (ins: instruction) (stk: cstk): bool :=
  match ins with
  | Pret =>
    match stk with
    | [] => true
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

Definition compare_final_state (rs: regset) (h: list int64) (addr_map: list addr_region): bool :=
  match List.nth_error h 0%nat with
  | None => false
  | Some v => is_abstract_value_concrete_eq (rs R0) v addr_map
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
  compare_trace_at_pc_aux R10 rs trace addr_map.

Fixpoint bpf_interpreter_trace_check (fuel: nat) (addr_map: list addr_region) (init_sp: int64)  
  (bpf_prog: ebpf_prog) (trace: list (list int64)) (st: outcome): bool :=
  match fuel with
  | O => debug_fail_common "Fuel exhausted" (* assume we have fenouagh fuell *)
  | S k =>
    match st with
    | Stuck => debug_fail_common "Stuck from start"
    | Next rs stk code_id tail_call_cnt m =>
      match rs PC with
      | Vptr b ofs =>
        match find_code code_id bpf_prog with
        | None => debug_fail_common "find_code failed"
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
              | [] => debug_fail_common "Trace ended before program finished"
              | h :: t =>
                (* Here we get R0 from current state *)
                match List.nth_error h 0%nat with
                | None => debug_fail_common "No R0 found in trace"
                | Some r0 =>
                (** TODO: we assume the return value is Vlong, but it is possible to be a pointer *)
                  bpf_interpreter_trace_check k addr_map init_sp bpf_prog t
                    (Next (nextinstr (rs#R0 <- (Vlong r0))) stk code_id tail_call_cnt m)
                end
              end
            | _ =>
              if is_final_state ins stk then
                match trace with
                | [] => true
                 (*| [h] => if compare_final_state rs h addr_map then true
                         else debug_fail_exec 2 ofs ins rs (Pregmap.init (Vlong Int64.zero)) h addr_map *)
                | _ => debug_fail_common "Program finished before trace ended"
                end
              else
                let next_st := exec_instr bpf_prog ins rs stk code_id tail_call_cnt m addr_map in
                  match next_st with
                  | Stuck =>
                    match trace with
                    | [] => debug_fail_common "Trace ended before program finished"
                    | h :: t => debug_fail_exec 1 ofs ins rs rs h addr_map
                    end
                  | Next rs_after stk_after code_id tail_call_cnt m_after =>
                    match trace with
                    | [] => debug_fail_common "Trace ended before program finished" (* (* The next instruction should be BPF_exit *) bpf_interpreter_trace_check k addr_map init_sp bpf_prog [] next_st *)
                    | h :: t => 
                      if compare_trace_at_pc rs_after h addr_map then
                        bpf_interpreter_trace_check k addr_map init_sp bpf_prog t next_st
                      else
                        debug_fail_exec 0 ofs ins rs rs_after h addr_map
                    end
                end
            end
          end
        end
      | _ => debug_fail_common "PC is not a pointer"
      end
    end
  end.

Definition create_initial_state (ctx stk pc: block): regset :=
  (* (Pregmap.init (Vlong Int64.zero)) *)
  (Pregmap.init Vundef)
    # PC <- (Vptr pc Ptrofs.zero)
    # R10 <- (Vptr stk (Ptrofs.repr bpf_stack_size))
    (* # R10 <- (Vptr stk Ptrofs.zero) *)
    # R1 <- (Vptr ctx Ptrofs.zero)
    (* # BP  <- Vnullptr *)
.

Fixpoint create_jump_table (jmp_blk: block) (jmp_table: list (Z * int64 * code)) (addr_map: list addr_region) (m: mem): (list addr_region) * mem :=
  match jmp_table with
  | [] => (addr_map, m)
  | h1 :: tl =>
    let (info, h) := h1 in
      let (index, target) := info in
  (* we don't need to store the bytecode into memory as we directly access bpf_prog *)
    let (m1, pc_blk1) := Mem.alloc m 0 (Z.of_nat (8*(List.length h))) in
    let m2 :=
      match Mem.storev Mint64 m1 (Vptr jmp_blk (Ptrofs.repr (8*index))) (Vptr pc_blk1 Ptrofs.zero) with
      | None => (**should be impossible *) m1
      | Some m' => m'
      end
    in
    let addr_map := {| 
      base_blk := pc_blk1;
      size_blk := Z.of_nat (8*(List.length h));
      base_addr := target
    |} :: addr_map in
      create_jump_table jmp_blk tl addr_map m2
  end.

Fixpoint create_bpf_maps (bpf_maps: list (Z * int64)) (addr_map: list addr_region) (m: mem): (list addr_region) * mem :=
  match bpf_maps with
  | [] => (addr_map, m)
  | h :: tl =>
    let (m', map_blk1) := Mem.alloc m 0%Z (fst h) in (* for simpilification, assuming the size is 100 *)
    let addr_map' := {| 
      base_blk := map_blk1;
      size_blk := fst h;
      base_addr := snd h
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
    (** because the begin of semantics_validation has allocated the `stk_blk`, so here we first adding the addr_map, then allocate the next one *)
    let addr_map' := {| 
      base_blk := stk_blk;
      size_blk := bpf_stack_size;
      base_addr := Int64.sub h (Int64.repr bpf_stack_size)
    |} :: addr_map in

    let (m', stk_blk') := Mem.alloc m 0%Z bpf_stack_size in
      create_addr_map_sp stk_blk' tl addr_map' m'
  end.


Fixpoint user_jmp_table2formal (jmp_table: list (Z * int64 * code)) : nat -> option code :=
  match jmp_table with
  | [] => fun _ => None
  | h :: t =>
    fun i => if Nat.eqb i (Z.to_nat (fst (fst h))) then Some (snd h)
    else  (user_jmp_table2formal t) i
  end.

Definition semantics_validation (bpf_prog: code)
                                (ctx_ptr: int64)
                                (bpf_maps: list (Z * int64))
                                (trace: list (list int64))
                                (jmp_table_max: Z)
                                (jmp_table: int64 * list (Z * int64 * code))
                                (sp_list: list int64) : bool :=
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
  let (m4, jmp_blk) := Mem.alloc m3 0 (Z.of_nat (8*33)) (** TODO:  *) in

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
      base_addr := ctx_ptr
    |};
    {| 
      base_blk := jmp_blk;
      size_blk := Z.of_nat (8*33); (** TODO:  *) 
      base_addr := fst jmp_table
    |} ] in
  let (addr_map5, m5) := create_jump_table jmp_blk (snd jmp_table) addr_map m4 in
  let (addr_map6, m6) := create_bpf_maps bpf_maps addr_map5 m5 in

  let (addr_map', m') := create_addr_map_sp stk_blk sp_list addr_map6 m6 in
  let r10_base := match sp_list with | [] => (** should be impossible *) Int64.zero | h :: tl => h end in

  (** initial_regs *)
  let rs := create_initial_state ctx_blk stk_blk pc_blk in
  let init_st := (Next rs [] None 0%nat m') in (** None represents to execute the main_code *)

    bpf_interpreter_trace_check fuel addr_map' r10_base 
          {|  main_code := bpf_prog;
              jump_table := user_jmp_table2formal (snd jmp_table);
              max_entries := jmp_table_max |}
          trace init_st.
