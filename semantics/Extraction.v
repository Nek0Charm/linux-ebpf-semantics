Require Import Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import bpf.ebpf.ebpfBinSem.
Require Import Validation.

Extraction Language OCaml.

Extract Constant Archi.ptr64 => "true".
Extract Constant Archi.big_endian => "false".

Extraction Blacklist List String Int.

Extract Inlined Constant force_eval => "(fun a b -> let _ = a in b)".
Extract Constant debug_fail_common => "Debug_hooks.fail_common".
Extract Constant debug_fail_exec => "Debug_hooks.fail_exec".
Extract Constant debug_fail_decode => "Debug_hooks.fail_decode".
Extract Constant debug_fail_decode_oob => "Debug_hooks.fail_decode_oob".

Extraction "ebpf/validation.ml" semantics_validation.