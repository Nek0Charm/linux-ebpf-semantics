module Zarith = Z

open Validation
open Yojson.Safe.Util

(* ========================================== *)
(* 1. OCaml type to Coq type *)
(* ========================================== *)
let rec positive_of_uint64 n =
  if n = 0L then failwith "unreachable"
  else if n = 1L then XH
  else if Stdlib.Int64.logand n 1L = 0L then 
    XO (positive_of_uint64 (Stdlib.Int64.shift_right_logical n 1))
  else 
    XI (positive_of_uint64 (Stdlib.Int64.shift_right_logical n 1))

let coq_Z_of_int64 n =
  if n = 0L then Z0
  else Zpos (positive_of_uint64 n)

let compcert_int64_of_native (i: int64) =
  Int64.repr (coq_Z_of_int64 i)

let cast_list l = List.map compcert_int64_of_native l
let cast_trace t = List.map cast_list t

let coq_Z_of_int n =
  coq_Z_of_int64 (Stdlib.Int64.of_int n)

(* 转换 mem_block: (addr, size, ty) -> (nat * int64) *)
let cast_mem_blocks l =
  List.map (fun (size, addr) -> 
    (coq_Z_of_int size, compcert_int64_of_native addr)
  ) l

(* 转换 jmp_table: (map_ptr, [(index, target, insns)]) -> (int64, ((nat * int64) * list int64) list) *)
let cast_jmp_table (map_ptr, l) =
  (compcert_int64_of_native map_ptr,
  List.map (fun (index, target, insns) ->
    ((coq_Z_of_int index, compcert_int64_of_native target), cast_list insns)
  ) l)

(* ========================================== *)
(* 2. JSON Parser *)
(* ========================================== *)
let parse_uint64 json_node =
  let z_to_int64 z =
    let two_64 = Zarith.shift_left Zarith.one 64 in
    let z_masked = Zarith.logand z (Zarith.pred two_64) in
    let max_signed = Zarith.shift_left Zarith.one 63 in
    if Zarith.geq z_masked max_signed then
      Zarith.to_int64 (Zarith.sub z_masked two_64)
    else
      Zarith.to_int64 z_masked
  in

  match json_node with
  | `Int i -> Stdlib.Int64.of_int i
  | `Intlit s -> z_to_int64 (Zarith.of_string s) 
  | `String s -> z_to_int64 (Zarith.of_string s)
  | _ -> failwith "Invalid number format in JSON"

(* 解析内存块对象 *)
let parse_mem_block node =
  let base_addr = node |> member "base_addr" |> parse_uint64 in
  let size = node |> member "size" |> to_int in
  (size, base_addr)

(* 解析跳转表条目 *)
let parse_jmp_entry node =
  let index = node |> member "index" |> to_int in
  let target = node |> member "target" |> parse_uint64 in
  let insns = node |> member "insns" |> to_list |> List.map parse_uint64 in
  (index, target, insns)

let parse_single_program prog_node =
  let prog_name = prog_node |> member "prog_name" |> to_string in
  
  (* 对应新的字段名 "prog_insn" *)
  let prog_insn = 
    prog_node |> member "prog_insn" |> to_list |> List.map parse_uint64 
  in
  
  (* 对应新的 Trace 结构：直接是 string list list *)
  let trace_nodes = prog_node |> member "trace" |> to_list in
  let trace = 
    List.map (fun t_node ->
      t_node |> to_list |> List.map parse_uint64
    ) trace_nodes 
  in

  let sp_list = 
    prog_node |> member "sp_list" |> to_list |> List.map parse_uint64
  in

  let ctx_ptr =
    prog_node |> member "ctx_ptr" |> parse_uint64
  in

  let mem_blocks = 
    prog_node |> member "mem_blocks" |> to_list |> List.map parse_mem_block 
  in
  
  let jmp_max_entries =
    prog_node |> member "jmp_max_entries" |> to_int
  in

  let jmp_table = (
    prog_node |> member "jmp_map_ptr" |> parse_uint64,
    prog_node |> member "jmp_table" |> to_list |> List.map parse_jmp_entry 
  )
  in
  
  (prog_name, prog_insn, trace, sp_list, ctx_ptr, mem_blocks, jmp_max_entries, jmp_table)

let load_traces_from_json filename =
  let path = Printf.sprintf "../trace/%s.json" filename in
  let json = Yojson.Safe.from_file path in
  json |> to_list |> List.map parse_single_program

(* ========================================== *)
(* 3. Main Testing Program *)
(* ========================================== *)

let run_test filename verbose =
  Debug_printer.init_hooks verbose;
  if verbose then Printf.printf "Loading JSON traces from %s...\n" filename;
  
  let programs = load_traces_from_json filename in
  let total_progs = List.length programs in
  
  if verbose then Printf.printf "[Info] Successfully loaded %d programs.\n\n" total_progs;
  
  let passed_count = ref 0 in

  List.iteri (fun i (prog_name, prog_mock, trace_mock, sp_list, ctx_ptr, mem_blocks, jmp_max_entries, jmp_table) ->
    if verbose then begin
      Printf.printf "=================================================\n";
      Printf.printf "Validating Program [%d]: %s\n" (i + 1) prog_name;
      Printf.printf "  - Instructions : %d\n" (List.length prog_mock);
      Printf.printf "  - Trace steps  : %d\n" (List.length trace_mock)
    end;

    (* Constuct initial state and align the timeline *)
    (* let aligned_trace_mock =
        let r1_ctx = ctx_ptr in
        let r10_stk = List.hd sp_list in
        (* Initial state：R1 and R10 are initialized, others are 0 *)
        let init_regs = [0L; r1_ctx; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; r10_stk; 0L] in
        init_regs :: trace_mock
    in *)

    let result = semantics_validation 
                    (cast_list prog_mock)
                    (compcert_int64_of_native ctx_ptr)
                    (cast_mem_blocks mem_blocks)
                    (cast_trace trace_mock)
                    (coq_Z_of_int jmp_max_entries)
                    (cast_jmp_table jmp_table)
                    (cast_list sp_list)
                    
    in
    
    if result then begin
      incr passed_count;
      if verbose then Printf.printf "  [+] Result: PASSED (Execution matches formal semantics)\n"
    end else begin
      if verbose then Printf.printf "  [-] Result: FAILED (Trace mismatch or execution stuck)\n"
    end
  ) programs;
  
  if verbose then begin
    Printf.printf "=================================================\n";
    Printf.printf "All validations finished. Passed: %d / %d\n" !passed_count total_progs
  end else begin
    Printf.printf "[%s] Passed: %d / %d\n" filename !passed_count total_progs;
    flush stdout
  end

let () =
  if not !Sys.interactive then begin
    if Array.length Sys.argv < 2 then
      Printf.printf "Usage: %s <trace_filename | test_progs>\n" Sys.argv.(0)
    else
      let arg = Sys.argv.(1) in
      if arg = "test_progs" || arg = "test_bpf" then begin
        let dir_path = "../trace/" ^ arg ^ "/" in
        try
          (* 1. 获取目录下所有文件 *)
          let files = Sys.readdir dir_path in
          (* 2. 过滤出 .json 文件并去掉后缀，然后排序 *)
          let test_names = 
            Array.to_list files
            |> List.filter (fun f -> Filename.check_suffix f ".json")
            |> List.map (fun f -> Filename.chop_suffix f ".json")
            |> List.sort String.compare
          in
          
          Printf.printf "Starting batch validation for %d programs in %s...\n\n" 
            (List.length test_names) dir_path;
            
          (* 3. 逐个执行 run_test，路径拼接为 "test_progs/文件名" *)
          List.iter (fun name -> 
            run_test (Printf.sprintf "%s/%s" arg name) false
          ) test_names;
          
          Printf.printf "\nBatch validation for %s finished.\n" arg
        with
        | Sys_error msg -> Printf.printf "Error accessing directory: %s\n" msg
        | e -> Printf.printf "An unexpected error occurred: %s\n" (Printexc.to_string e)
      end else begin
        (* 如果不是 test_progs，则视为单个文件名执行 *)
        run_test arg true
      end
  end