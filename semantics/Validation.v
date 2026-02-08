From Coq Require Import ZArith List.

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.

From bpf.ebpf Require Import ebpfBinSem.

Import ListNotations.


Axiom find_instr: Z -> code -> option instruction.
Fixpoint bpf_interpreter (fuel: nat) (bpf_prog: list byte) (st: outcome): outcome :=
  match fuel with
  | O => Stuck (* assume we have enough fuel *)
  | S k =>
    match st with
    | Stuck => Stuck
    | Next rs m =>
      match rs PC with
      | Vptr b ofs =>
        match find_instr (Ptrofs.unsigned ofs) bpf_prog with
        | None => Stuck
        | Some i => bpf_interpreter k bpf_prog (exec_instr i rs m)
        end
      | _ => Stuck
      end
    end
  end.

Fixpoint find_concrete_address (b: block) (addr_map: list (block * int64)): option int64 :=
  match addr_map with
  | [] => None
  | h :: t =>
    if Pos.eqb (fst h) b then
      Some (snd h)
    else
      find_concrete_address b t
  end.

Fixpoint find_abstract_address (v: int64) (addr_map: list (block * int64)): option block :=
  match addr_map with
  | [] => None
  | h :: t =>
    if Int64.eq (snd h) v then
      Some (fst h)
    else
      find_abstract_address v t
  end.

Definition cast_address_abs_to_concrete (addr: val) (addr_map: list (block * int64)): option int64 :=
  match addr with
  | Vptr b ofs =>
    match find_concrete_address b addr_map with
    | None => None
    | Some v => Some (Int64.add v (Ptrofs.to_int64 ofs))
    end
  | _ => None
  end.

Definition is_final_state (ins: instruction) (rs: regset) (addr_map: list (block * int64)) (init_sp: int64): bool :=
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
Definition is_abstract_value_concrete_eq (av: val) (cv: int64) (addr_map: list (block * int64)): bool :=
  match av with
  | Vlong i => Int64.eq cv i
  | Vptr b ofs =>
    match cast_address_abs_to_concrete (Vptr b ofs) addr_map with
    | None => false
    | Some i => Int64.eq cv i
    end
  | _ => false
  end.

Definition compare_final_state (rs: regset) (trace: list (list int64)) (addr_map: list (block * int64)): bool :=
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

Definition compare_trace_at_pc_aux (r: ireg) (rs: regset) (trace: list int64) (addr_map: list (block * int64)): bool :=
  match List.nth_error trace (nat_of_ireg r) with
  | None => false
  | Some cv => is_abstract_value_concrete_eq (rs r) cv addr_map
  end.

Definition compare_trace_at_pc (rs: regset) (trace: list int64) (addr_map: list (block * int64)): bool :=
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

Fixpoint bpf_interpreter_trace_check (fuel: nat) (addr_map: list (block * int64)) (init_sp: int64)  
  (bpf_prog: list byte) (trace: list (list int64)) (st: outcome): bool :=
  match fuel with
  | O => false (* assume we have fenouagh fuell *)
  | S k =>
    match st with
    | Stuck => false
    | Next rs m =>
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
                bpf_interpreter_trace_check k addr_map init_sp bpf_prog trace
                  (Next (nextinstr (rs#R0 <- (Vlong r0))) m)
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
                  bpf_interpreter_trace_check k addr_map init_sp bpf_prog t (exec_instr ins rs m)
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
    # BP  <- Vnullptr.

Definition semantics_validation_aux (bpf_prog: list byte) (trace: list (list int64)) (ctx_base r10_base : int64): bool :=
  (** assume some information, only for testing *)
  let fuel := 1000 %nat in (* fixed fuel *)
  let ctx_size := 1000 %Z in (* fixed context memort size *)

  (** initial_mem *)
  let m0 := Mem.empty in
  let (m1, pc_blk) := Mem.alloc m0 0 (Z.of_nat (List.length bpf_prog)) in
  let (m2, ctx_blk) := Mem.alloc m1 0 ctx_size in
  let (m3, stk_blk) := Mem.alloc m2 0 bpf_stack_size in

  (** addr_map: TODO we assume pc address is 0 here *)
  let addr_map := [(pc_blk, Int64.zero); (ctx_blk, ctx_base); (stk_blk, r10_base)] in

  (** initial_regs *)
  let rs := create_initial_state ctx_blk stk_blk pc_blk in

    bpf_interpreter_trace_check fuel addr_map r10_base bpf_prog trace (Next rs m3).

(** trace stores [R0-R10] values executed by core.c of Linux eBPF VM *)
Definition semantics_validation (bpf_prog: list byte) (trace: list (list int64)): bool :=
  match trace with
  | [] => false
  | h :: t =>
    match List.nth_error h 1%nat with
    | None => false
    | Some ctx_base =>
      match List.nth_error h 10%nat with
      | None => false
      | Some r10_base =>
        semantics_validation_aux bpf_prog trace ctx_base r10_base
      end
    end
  end.