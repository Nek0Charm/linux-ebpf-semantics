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

(* Convert mem_block: (addr, size, ty) -> (nat * int64). *)
let cast_mem_blocks l =
  List.map (fun (size, addr) -> 
    (coq_Z_of_int size, compcert_int64_of_native addr)
  ) l

(* Convert jmp_table:
   (map_ptr, [(index, target, insns)])
   -> (int64, ((nat * int64) * list int64) list). *)
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

(* Parse a memory-block object. *)
let parse_mem_block node =
  let base_addr = node |> member "base_addr" |> parse_uint64 in
  let size = node |> member "size" |> to_int in
  (size, base_addr)

(* Parse a jump-table entry. *)
let parse_jmp_entry node =
  let index = node |> member "index" |> to_int in
  let target = node |> member "target" |> parse_uint64 in
  let insns = node |> member "insns" |> to_list |> List.map parse_uint64 in
  (index, target, insns)

let parse_single_program prog_node =
  let prog_name = prog_node |> member "prog_name" |> to_string in
  
  (* Use the new "prog_insn" field name. *)
  let prog_insn = 
    prog_node |> member "prog_insn" |> to_list |> List.map parse_uint64 
  in
  
  (* The new trace representation is a string list list. *)
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

let load_traces_from_json trace_root filename =
  let path = Filename.concat trace_root (filename ^ ".json") in
  let json = Yojson.Safe.from_file path in
  to_list json

let parse_helper_return = function
  | `Int i when i >= 0 -> Stdlib.Int64.of_int i
  | `Intlit s | `String s ->
      (* OCaml uses 0u for decimal inputs spanning the full uint64 range. *)
      let literal =
        if String.starts_with ~prefix:"0x" s || String.starts_with ~prefix:"0X" s
        then s else "0u" ^ s
      in
      (try Stdlib.Int64.of_string literal
       with Failure _ -> failwith ("Invalid uint64: " ^ s))
  | _ -> failwith "Expected an unsigned 64-bit integer"

let helper_event_matches run event =
  try
    let code_id = event |> member "code_id" |> to_int in
    let pc = event |> member "pc" |> to_int in
    let index = event |> member "trace_index" |> to_int in
    let id = event |> member "helper_id" |> to_int in
    let code = match member "codes" run with
      | `Null when code_id = 0 -> run
      | codes -> codes |> to_list |> List.find (fun c -> member "code_id" c = `Int code_id)
    in
    let insns =
      (if code = run then member "prog_insn" run else member "insns" code)
      |> to_list |> List.map parse_uint64 in
    let call_matches calls =
      match calls |> to_list |> List.filter (fun call -> member "pc" call = `Int pc) with
      | [call] -> member "helper_id" call = `Int id | _ -> false in
    let unique field = member "helper_events" run |> to_list |> List.filter (fun other ->
      member field other = member field event) |> List.length |> fun count -> count = 1 in
    let row = run |> member "trace" |> to_list |> fun rows -> List.nth rows index |> to_list in
    code_id >= 0 && pc >= 0 && index >= 0 && id >= 0 &&
    (member "call_id" event |> to_int) >= 0 && unique "call_id" && unique "trace_index" &&
    (code_id <> 0 || insns = (member "prog_insn" run |> to_list |> List.map parse_uint64)) &&
    call_matches (member "helper_calls" code) &&
    (code_id <> 0 || member "helper_calls" run = `Null || call_matches (member "helper_calls" run)) &&
    Stdlib.Int64.logand (List.nth insns pc) 0xffffffffL = 0x85L &&
    parse_helper_return (member "ret" event) = parse_uint64 (List.hd row)
  with Failure _ | Invalid_argument _ | Not_found | Type_error _ -> false

let validate_helper_event spec run event =
  if not (helper_event_matches run event) then Some false else
  match spec.helper_post with
  | MemoryPost _ -> None  (* Requires reconstructed registers and memory. *)
  | NoMemoryEffect _ ->
      if member "premem" event <> `List [] || member "postmem" event <> `List []
         || member "map_effect" event <> `Null then Some false
      else
        let ret = event |> member "ret" |> parse_helper_return in
        helper_validation spec None (Vlong (compcert_int64_of_native ret)) SameMemory

let read_helper_events run = run |> member "helper_events" |> to_list

let capture_complete node = member "capture_status" node = `String "complete"

(* ========================================== *)
(* 3. Main Testing Program *)
(* ========================================== *)

let validate_legacy_traces ?(validate = semantics_validation)
    ?(complete = fun () -> true) filename verbose programs =
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

    let result = validate
                    (cast_list prog_mock)
                    (compcert_int64_of_native ctx_ptr)
                    (cast_mem_blocks mem_blocks)
                    (cast_trace trace_mock)
                    (coq_Z_of_int jmp_max_entries)
                    (cast_jmp_table jmp_table)
                    (cast_list sp_list) && complete ()
                    
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
  end;
  (!passed_count, total_progs)

let validate_helper_run filename verbose run =
  let events = read_helper_events run in
  let valid_events = List.for_all (helper_event_matches run) events in
  if not valid_events then begin
    Printf.printf "[%s] Helper events have inconsistent, duplicate, or invalid call locations.\n%!" filename;
    (0, 1)
  end else if not (capture_complete run) ||
      not (List.for_all (fun event -> capture_complete event &&
        Option.bind (find_helper (coq_Z_of_int (member "helper_id" event |> to_int)))
          (fun spec -> validate_helper_event spec run event) = Some true) events) then
    (0, 1)
  else if List.exists (fun field -> match member field run with
      | `Null | `List [] -> false | _ -> true) ["maps"; "initial_memory"] then begin
    Printf.printf "[%s] Execution not validated: captured map/initial memory is not reconstructed.\n%!" filename;
    (0, 1)
  end else
    let trace = member "trace" run |> to_list in
    let consumed = Hashtbl.create (List.length events) in
    let check_helper code_id pc remaining =
      let index = List.length trace - List.length remaining in
      match List.find_opt (fun event -> member "trace_index" event = `Int index) events with
      | Some event when code_id = None && member "code_id" event = `Int 0 &&
          pc = coq_Z_of_int (member "pc" event |> to_int) ->
          Hashtbl.replace consumed index (); true
      | _ -> false
    in
    let default name value fields =
      if List.assoc_opt name fields = None then (name, value) :: fields else fields in
    let sp = match trace with
      | row :: _ -> `List [row |> to_list |> fun values -> List.nth values 10]
      | [] -> `List [] in
    let normalized = to_assoc run |> default "sp_list" sp
      |> default "jmp_max_entries" (`Int 0) |> default "jmp_map_ptr" (`String "0x0") in
    validate_legacy_traces ~validate:(semantics_validation_with_helper_check check_helper)
      ~complete:(fun () -> Hashtbl.length consumed = List.length events)
      filename verbose [parse_single_program (`Assoc normalized)]

let run_test trace_root filename verbose =
  Debug_printer.init_hooks verbose;
  if verbose then Printf.printf "Loading JSON traces from %s...\n" filename;
  let runs = load_traces_from_json trace_root filename in
  let helper_runs, legacy_runs = List.partition
    (fun run -> List.mem_assoc "helper_events" (to_assoc run)) runs in
  let legacy_passed, _ = if legacy_runs = [] then (0, 0) else
    validate_legacy_traces filename verbose (List.map parse_single_program legacy_runs) in
  if helper_runs <> [] then begin
    let event_count =
      List.fold_left (fun count run -> count + List.length (read_helper_events run)) 0 helper_runs
    in
    let complete_runs = List.filter capture_complete helper_runs in
    let complete_events =
      List.concat_map (fun run -> read_helper_events run |> List.filter capture_complete
        |> List.map (fun event -> (run, event))) complete_runs
    in
    let distinct_ids =
      complete_events
      |> List.map (fun (_, event) -> event |> member "helper_id" |> to_int)
      |> List.sort_uniq compare |> List.map string_of_int |> String.concat ", "
    in
    Printf.printf "[%s] Complete runs: %d / %d. Helper events with complete run and event capture: %d / %d (IDs: %s).\n%!"
      filename (List.length complete_runs) (List.length helper_runs)
      (List.length complete_events) event_count
      (if distinct_ids = "" then "none" else distinct_ids);
    let passed, failed, unsupported =
      List.fold_left (fun (passed, failed, unsupported) (run, event) ->
        let id = event |> member "helper_id" |> to_int in
        let verdict = Option.bind (find_helper (coq_Z_of_int id))
                        (fun spec -> validate_helper_event spec run event) in
        match verdict with
        | None -> (passed, failed, unsupported + 1)
        | Some true -> (passed + 1, failed, unsupported)
        | Some false ->
            Printf.printf "[%s] Helper ID %d call %d violates its specification.\n%!"
              filename id (event |> member "call_id" |> to_int);
            (passed, failed + 1, unsupported)
      ) (0, 0, 0) complete_events
    in
    Printf.printf "[%s] Helper checks: %d passed, %d failed. Unsupported helper calls: %d.\n%!"
      filename passed failed unsupported;
    let helper_passed = List.fold_left (fun count run ->
      try count + fst (validate_helper_run filename verbose run)
      with Failure message | Invalid_argument message ->
        Printf.printf "[%s] Invalid helper capture: %s\n%!" filename message; count
      | Type_error (message, _) ->
        Printf.printf "[%s] Invalid helper capture: %s\n%!" filename message; count
    ) 0 helper_runs in
    (legacy_passed + helper_passed, List.length runs)
  end else (legacy_passed, List.length runs)

let parse_cli () =
  let trace_root = ref "trace" in
  let target = ref None in
  let set_target value =
    match !target with
    | None -> target := Some value
    | Some _ -> raise (Arg.Bad "only one trace target may be specified")
  in
  let options = [
    ("--trace-root", Arg.Set_string trace_root,
      "DIR directory containing test_progs/ and test_bpf/")
  ] in
  let usage =
    Printf.sprintf "Usage: %s [--trace-root DIR] <trace_filename | test_progs | test_bpf>"
      Sys.argv.(0)
  in
  Arg.parse options set_target usage;
  match !target with
  | Some value -> (!trace_root, value)
  | None -> raise (Arg.Bad "a trace target is required")

let () =
  if not !Sys.interactive then begin
      let trace_root, arg = parse_cli () in
      if arg = "test_progs" || arg = "test_bpf" then begin
        let dir_path = Filename.concat trace_root arg in
        try
          (* 1. Read every file in the directory. *)
          let files = Sys.readdir dir_path in
          (* 2. Keep .json files, remove the suffix, and sort them. *)
          let test_names = 
            Array.to_list files
            |> List.filter (fun f -> Filename.check_suffix f ".json")
            |> List.map (fun f -> Filename.chop_suffix f ".json")
            |> List.sort String.compare
          in
          
          Printf.printf "Starting batch validation for %d programs in %s...\n\n" 
            (List.length test_names) dir_path;
            
          let total_passed = ref 0 in
          let total_cases = ref 0 in
          
          (* 3. Run each test with a path such as "test_progs/filename". *)
          List.iter (fun name -> 
            let (p, c) =
              run_test trace_root (Filename.concat arg name) false
            in
            total_passed := !total_passed + p;
            total_cases := !total_cases + c
          ) test_names;
          
          Printf.printf "\nBatch validation for %s finished. Total Passed: %d / %d\n" arg !total_passed !total_cases;
          if !total_passed < !total_cases then exit 1
        with
        | Sys_error msg -> Printf.printf "Error accessing directory: %s\n" msg; exit 1
        | e -> Printf.printf "An unexpected error occurred: %s\n" (Printexc.to_string e); exit 1
      end else begin
        (* Otherwise, treat the argument as a single trace filename. *)
        let passed, total = run_test trace_root arg true in
        if passed < total then exit 1
      end
  end
