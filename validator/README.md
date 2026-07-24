# Semantic Validation

The Coq files in this directory use the internal logical namespace
`bpf.validator` and depend on the public `bpf.semantics` theory.

## Build & Run

```shell
make validation
```

See overall result:

```shell
dune exec validator/main.exe -- --trace-root trace test_progs
```

See one result:

```shell
dune exec validator/main.exe -- --trace-root trace test_progs/verifier_and
```

`--trace-root` may be absolute or relative to the current working directory,
so the executable does not rely on being launched from a specific directory.

## Validate Newly Generated Traces

After running the Linux observer with `--suite all`, point `--trace-root` at
the generated result directory:

```shell
RESULTS=../../linux/tools/testing/selftests/bpf/tracer/results/<timestamp>-all

dune exec validator/main.exe -- --trace-root "$RESULTS" test_progs
dune exec validator/main.exe -- --trace-root "$RESULTS" test_bpf
```

To inspect one generated trace:

```shell
dune exec validator/main.exe -- \
  --trace-root "$RESULTS" test_progs/verifier_and
```

Batch validation reads only JSON files directly under `test_progs/` or
`test_bpf/`; quarantined files in `empty/` and `error/` are ignored.

## Debug (using utop)

Change the last line in `validator/.ocamlinit`.

```ocaml
#trace Validation.exec_instr;; (* change to some function you want to trace *)
```

Then enter utop console:


```shell
cd validator
dune utop --root ..
```

In utop console:

```shell
run_test "../trace" "test_progs/verifier_and" true;;
```
