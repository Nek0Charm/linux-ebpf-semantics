let fail_common_hook = ref (fun (_: string) -> false)
let fail_common msg = !fail_common_hook msg

let fail_exec_hook = ref (fun (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) (_: Obj.t) -> false)
let fail_exec err_code pc ins rs_before rs_after expected_trace addr_map = 
  !fail_exec_hook (Obj.repr err_code) (Obj.repr pc) (Obj.repr ins) (Obj.repr rs_before) (Obj.repr rs_after) (Obj.repr expected_trace) (Obj.repr addr_map)
let fail_decode_hook = ref (fun (_: Obj.t) (_: Obj.t) -> false)
let fail_decode pc raw_insn = !fail_decode_hook (Obj.repr pc) (Obj.repr raw_insn)

let fail_decode_oob_hook = ref (fun (_: Obj.t) -> false)
let fail_decode_oob pc = !fail_decode_oob_hook (Obj.repr pc)
