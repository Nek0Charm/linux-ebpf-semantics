# Semantic Validation

## Build & Run

```shell
make
cd semantics
dune build
```

See overall result:

```shell
dune exec ./main.exe test_progs
```

See one result:

```shell
dune exec ./main.exe test_progs/verifier_and
```

## Debug (using utop)

Change the last line in `semantics/.ocamlinit`.

```ocaml
#trace Validation.exec_instr;; (* change to some function you want to trace *)
```

Then enter utop console:


```shell
dune utop
```

In utop console:

```shell
run_test "test_progs__verifier_and" true;;
```
