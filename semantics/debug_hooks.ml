let fail_common_hook = ref (fun (_: Obj.t) -> false)
let debug_fail_common (msg: string) =
  Printf.printf "\n[Trace Check Failed: COMMON ERROR]\n";
  Printf.printf "  => Reason: %s\n" msg;
  false

let fail_step_hook = ref (fun (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) -> false)
let fail_step pc r0 r1 r2 r10 = 
  !fail_step_hook (Obj.repr pc) (Obj.repr r0) (Obj.repr r1) (Obj.repr r2) (Obj.repr r10)

let fail_stuck_hook = ref (fun (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) -> false)
let fail_stuck pc r0 r1 r2 r10 = 
  !fail_stuck_hook (Obj.repr pc) (Obj.repr r0) (Obj.repr r1) (Obj.repr r2) (Obj.repr r10)

let fail_final_hook = ref (fun (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) -> false)
let fail_final pc r0 r1 r2 r10 = 
  !fail_final_hook (Obj.repr pc) (Obj.repr r0) (Obj.repr r1) (Obj.repr r2) (Obj.repr r10)

let fail_decode_hook = ref (fun (_: Obj.t) (_: Obj.t) -> false)
let fail_decode pc raw_insn = !fail_decode_hook (Obj.repr pc) (Obj.repr raw_insn)

let fail_decode_oob_hook = ref (fun (_: Obj.t) -> false)
let fail_decode_oob pc = !fail_decode_oob_hook (Obj.repr pc)
