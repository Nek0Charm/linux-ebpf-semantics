open Validation

(* ==== 1. Coq type to OCaml type ==== *)
let rec int64_of_positive = function
  | XH -> 1L
  | XO p -> Stdlib.Int64.shift_left (int64_of_positive p) 1
  | XI p -> Stdlib.Int64.logor (Stdlib.Int64.shift_left (int64_of_positive p) 1) 1L

let int64_of_coq_Z = function
  | Z0 -> 0L
  | Zpos p -> int64_of_positive p
  | Zneg p -> Stdlib.Int64.neg (int64_of_positive p)

let rec int_of_coq_nat = function
  | Validation.O -> 0
  | Validation.S n -> 1 + int_of_coq_nat n

let string_of_char_list chars =
  String.of_seq (List.to_seq chars)

(* ==== 2. debug state printer ==== *)

(* ==== 2.1. instruction's printer ==== *)

let string_of_reg (r: Validation.ireg) =
  match r with
  | Validation.R0 -> "r0"  | Validation.R1 -> "r1"
  | Validation.R2 -> "r2"  | Validation.R3 -> "r3"
  | Validation.R4 -> "r4"  | Validation.R5 -> "r5"
  | Validation.R6 -> "r6"  | Validation.R7 -> "r7"
  | Validation.R8 -> "r8"  | Validation.R9 -> "r9"
  | Validation.R10 -> "r10" | Validation.RAX -> "rax"

let int64_of_imm (i: Validation.imm) = int64_of_coq_Z (Obj.magic i : Validation.z)
let int64_of_off (o: Validation.off) = int64_of_coq_Z (Obj.magic o : Validation.z)

let string_of_reg_or_imm (src: (Validation.ireg, Validation.imm) Validation.sum) =
  match src with
  | Validation.Inl r -> string_of_reg r
  | Validation.Inr i -> Printf.sprintf "%Ld" (int64_of_imm i)

let string_of_aluOp (op: Validation.aluOp) =
  match op with
  | Validation.ADD -> "+="   | Validation.SUB -> "-="
  | Validation.MUL -> "*="   | Validation.DIV -> "/="
  | Validation.SDIV -> "s/=" | Validation.OR -> "|="
  | Validation.AND -> "&="   | Validation.LSH -> "<<="
  | Validation.RSH -> ">>="  | Validation.NEG -> "~"
  | Validation.MOD -> "%="   | Validation.SMOD -> "s%="
  | Validation.XOR -> "^="   | Validation.MOV -> "="
  | Validation.MOVSX _ -> "= (movsx)"
  | Validation.ARSH -> "s>>="
  | Validation.END _ -> "bswap"

let string_of_cmpOp (op: Validation.cmpOp) =
  match op with
  | Validation.EQ -> "=="     | Validation.NE -> "!="
  | Validation.SET -> "&"     | Validation.GT _ -> ">"
  | Validation.GE _ -> ">="   | Validation.LT _ -> "<"
  | Validation.LE _ -> "<="

let string_of_sizeOp (sz: Validation.sizeOp) =
  match sz with
  | Validation.Byte0 -> "8"    | Validation.HalfWord -> "16"
  | Validation.Word -> "32"   | Validation.DBWord -> "64"

let string_of_insn (ins: Validation.instruction) =
  match ins with
  | Validation.Plddw (_, dst, lo, hi) ->
      Printf.sprintf "lddw %s, 0x%Lx%08Lx" 
        (string_of_reg dst) (int64_of_imm hi) (int64_of_imm lo)

  | Validation.Pload (sz, dst, src, off) ->
      Printf.sprintf "load%s %s, [%s %s %Ld]"
        (string_of_sizeOp sz) (string_of_reg dst) (string_of_reg src)
        (if int64_of_off off >= 0L then "+" else "") (int64_of_off off)

  | Validation.Pstore (sz, dst, src, off) ->
      Printf.sprintf "store%s [%s %s %Ld], %s"
        (string_of_sizeOp sz) (string_of_reg dst) 
        (if int64_of_off off >= 0L then "+" else "") (int64_of_off off)
        (string_of_reg_or_imm src)

  | Validation.Palu (op, w, dst, src) ->
      let w_str = match w with Validation.W32 -> "32" | Validation.W64 -> "64" in
      Printf.sprintf "alu%s: %s %s %s" 
        w_str (string_of_reg dst) (string_of_aluOp op) (string_of_reg_or_imm src)

  | Validation.Pjmp32 (imm) ->
      Printf.sprintf "jmp32 %Ld" (int64_of_imm imm)

  | Validation.Pjmp64 (off) ->
      Printf.sprintf "jmp %Ld" (int64_of_off off)

  | Validation.Pjmpcmp (op, w, dst, src, off) ->
      let w_str = match w with Validation.W32 -> "32" | Validation.W64 -> "64" in
      Printf.sprintf "jmp%s: if %s %s %s goto %Ld"
        w_str (string_of_reg dst) (string_of_cmpOp op) 
        (string_of_reg_or_imm src) (int64_of_off off)

  | Validation.Pcall (_, imm) ->
      Printf.sprintf "call %Ld" (int64_of_imm imm)

  | Validation.Pret -> 
      "exit (return)"

  | Validation.Ptail_call -> 
      "tail_call"

  | Validation.Pno_spec -> 
      "nop (no_spec)"

  (* 其他比较生僻或暂未使用的探测/原子指令 *)
  | Validation.Ploadsx _ -> "<loadsx>"
  | Validation.Pload_probe _ -> "<load_probe>"
  | Validation.Ploadsx_probe _ -> "<loadsx_probe>"
  | Validation.Patomic _ -> "<atomic>"

(* ==== 2.2. value & regset & trace's printer ==== *)

let string_of_val = function
  | Vundef -> "Vundef"
  | Vint i -> Printf.sprintf "Vint(%Ld)" (int64_of_coq_Z i)
  | Vlong l -> Printf.sprintf "Vlong(%Ld)" (int64_of_coq_Z l)
  | Vptr (b, ofs) -> Printf.sprintf "Vptr(block=%Ld, ofs=%Ld)" (int64_of_positive b) (int64_of_coq_Z ofs)
  | _ -> "Unsupported_Val"

let print_regset title (rs: Validation.ireg -> Validation.val0) =
  Printf.printf "  [%s]\n" title;
  Printf.printf "    R0  : %s\n" (string_of_val (rs Validation.R0));
  Printf.printf "    R1  : %s\n" (string_of_val (rs Validation.R1));
  Printf.printf "    R2  : %s\n" (string_of_val (rs Validation.R2));
  Printf.printf "    R3  : %s\n" (string_of_val (rs Validation.R3));
  Printf.printf "    R4  : %s\n" (string_of_val (rs Validation.R4));
  Printf.printf "    R5  : %s\n" (string_of_val (rs Validation.R5));
  Printf.printf "    R6  : %s\n" (string_of_val (rs Validation.R6));
  Printf.printf "    R7  : %s\n" (string_of_val (rs Validation.R7));
  Printf.printf "    R8  : %s\n" (string_of_val (rs Validation.R8));
  Printf.printf "    R9  : %s\n" (string_of_val (rs Validation.R9));
  Printf.printf "    R10 : %s\n" (string_of_val (rs Validation.R10));
  Printf.printf "    RAX : %s\n" (string_of_val (rs Validation.RAX))

let print_expected_trace expected_trace =
  Printf.printf "  [Expected JSON Trace State]\n";
  List.iteri (fun i v ->
    if i <= 10 then 
      Printf.printf "    R%d  : %Ld\n" i (int64_of_coq_Z v) 
  ) expected_trace

let print_debug_state reason pc insn rs_before rs_after expected_trace =
  Printf.printf "\n================= DEBUG DUMP ====================\n";
  Printf.printf "[Trace Check Failed: %s]\n" reason;
  Printf.printf "  => PC Offset : %Ld\n" (int64_of_coq_Z pc);
  Printf.printf "  => Instr     : %s\n\n" (string_of_insn insn);
  
  print_regset "State BEFORE Execution" rs_before;
  Printf.printf "\n";
  print_regset "State AFTER Execution (Coq)" rs_after;
  Printf.printf "\n";
  print_expected_trace expected_trace;
  Printf.printf "=================================================\n"

(* ==== 3. init debug hooks ==== *)
let init_hooks () =
  Debug_hooks.fail_common_hook := (fun msg_obj ->
    let msg_chars = (Obj.magic msg_obj : char list) in
    Printf.printf "\n[Trace Check Failed: COMMON ERROR]\n";
    Printf.printf "  => Reason: %s\n" (string_of_char_list msg_chars);
    false
  );

  Debug_hooks.fail_exec_hook := (fun err_obj pc_obj ins_obj rs_before_obj rs_after_obj expected_obj -> 
    let err_code = int_of_coq_nat (Obj.magic err_obj : Validation.nat) in
    let reason = match err_code with
      | 0 -> "STEP MISMATCH"
      | 1 -> "EXECUTION STUCK"
      | 2 -> "FINAL STATE MISMATCH"
      | _ -> "UNKNOWN EXECUTION ERROR"
    in
    let pc = (Obj.magic pc_obj : Validation.z) in
    let insn = (Obj.magic ins_obj : Validation.instruction) in
    let rs_before = (Obj.magic rs_before_obj : Validation.ireg -> Validation.val0) in
    let rs_after = (Obj.magic rs_after_obj : Validation.ireg -> Validation.val0) in
    let expected = (Obj.magic expected_obj : Validation.z list) in 
    
    print_debug_state reason pc insn rs_before rs_after expected; 
    false
  );

  Debug_hooks.fail_decode_hook := (fun pc_obj insn_obj -> 
    let pc_z = (Obj.magic pc_obj : Validation.z) in
    let insn_z = (Obj.magic insn_obj : Validation.z) in
    Printf.printf "\n[Trace Check Failed: DECODE ERROR]\n";
    Printf.printf "  => PC Offset : %Ld\n" (int64_of_coq_Z pc_z);
    Printf.printf "  => Raw Instr : 0x%016Lx\n" (int64_of_coq_Z insn_z);
    false
  );

  Debug_hooks.fail_decode_oob_hook := (fun pc_obj -> 
    let pc_z = (Obj.magic pc_obj : Validation.z) in
    Printf.printf "\n[Trace Check Failed: PC OUT OF BOUNDS]\n";
    Printf.printf "  => PC Offset : %Ld\n" (int64_of_coq_Z pc_z);
    false
  )