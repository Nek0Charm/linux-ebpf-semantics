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

let rec coq_nat_of_int n =
  if n <= 0 then Validation.O 
  else Validation.S (coq_nat_of_int (n - 1))

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

let parse_single_program prog_node =
  let prog_name = prog_node |> member "prog_name" |> to_string in
  
  let bpf_prog = 
    prog_node |> member "bpf_prog" |> to_list |> List.map parse_uint64 
  in
  
  let trace_nodes = prog_node |> member "trace" |> to_list in
  let trace = 
    List.map (fun t ->
      t |> member "regs" |> to_list |> List.map parse_uint64
    ) trace_nodes 
  in

  let sp_list = 
    prog_node |> member "sp_list" |> to_list |> List.map parse_uint64
  in

  let ctx_ptr =
    prog_node |> member "ctx_ptr" |> parse_uint64
  in
  
  (prog_name, bpf_prog, trace, sp_list, ctx_ptr)

let load_traces_from_json filename =
  let path = Printf.sprintf "../trace/%s/%s_trace.json" filename filename in
  let json = Yojson.Safe.from_file path in
  json |> to_list |> List.map parse_single_program

(* ========================================== *)
(* 3. Main Testing Program *)
(* ========================================== *)
let read_lines filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true do
      let line = String.trim (input_line chan) in
      if String.length line > 0 then
        lines := line :: !lines
    done;
    []
  with End_of_file ->
    close_in chan;
    List.rev !lines

let run_test filename verbose =
  if verbose then Printf.printf "Loading JSON traces from %s...\n" filename;
  
  let programs = load_traces_from_json filename in
  let total_progs = List.length programs in
  
  if verbose then Printf.printf "[Info] Successfully loaded %d programs.\n\n" total_progs;
  
  let passed_count = ref 0 in

  List.iteri (fun i (prog_name, prog_mock, trace_mock, sp_list, ctx_ptr) ->
    if verbose then begin
      Printf.printf "=================================================\n";
      Printf.printf "Validating Program [%d]: %s\n" (i + 1) prog_name;
      Printf.printf "  - Instructions : %d\n" (List.length prog_mock);
      Printf.printf "  - Trace steps  : %d\n" (List.length trace_mock)
    end;

    (* Constuct initial state and align the timeline *)
    let aligned_trace_mock =
        let r1_ctx = ctx_ptr in
        let r10_stk = List.hd sp_list in
        (* Initial state：R1 and R10 are initialized, others are 0 *)
        let init_regs = [0L; r1_ctx; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; r10_stk] in
        init_regs :: trace_mock
    in

    let result = semantics_validation 
                    (cast_list prog_mock)
                    []
                    (coq_nat_of_int 0)
                    []
                    (cast_trace aligned_trace_mock)
                    (cast_list sp_list)
                    (compcert_int64_of_native ctx_ptr)
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
  Debug_printer.init_hooks ();
  if not !Sys.interactive then begin
    if Array.length Sys.argv < 2 then
      Printf.printf "Usage: %s <trace_filename | all>\n" Sys.argv.(0)
    else
      let arg = Sys.argv.(1) in
      if arg = "all" then begin
        let summary_file = "../trace/summary_with_trace.txt" in
        Printf.printf "Starting batch validation from %s...\n\n" summary_file;
        let filenames = read_lines summary_file in
        List.iter (fun f -> run_test f false) filenames;
        Printf.printf "\nBatch validation finished.\n"
      end else begin
        run_test arg true
      end
  end