Require Import Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import bpf.ebpf.ebpfBinSem.
Require Import Validation.

Extraction Language OCaml.

Extract Constant Archi.ptr64 => "true".
Extract Constant Archi.big_endian => "false".

Extraction Blacklist List String Int.

Extract Constant debug_fail_common => "Debug_hooks.fail_common".
Extract Constant debug_fail_step  => "Debug_hooks.fail_step".
Extract Constant debug_fail_stuck => "Debug_hooks.fail_stuck".
Extract Constant debug_fail_final => "Debug_hooks.fail_final".
Extract Constant debug_fail_decode => "Debug_hooks.fail_decode".
Extract Constant debug_fail_decode_oob => "Debug_hooks.fail_decode_oob".

Extraction "ebpf/validation.ml" semantics_validation.