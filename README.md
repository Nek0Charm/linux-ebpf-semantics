# Formalizing the Linux eBPF Core ISA: A Mechanized Operational Semantics and Real-world Application

## Code Structure

- `semantics/`: the eBPF state, syntax, semantics, and validation workflow
- `trace/`: execution traces from Linux kernel + Two Official Linux eBPF test suites (1. [progs](https://elixir.bootlin.com/linux/v7.0-rc4/source/tools/testing/selftests/bpf/progs) / [test_progs](https://elixir.bootlin.com/linux/v7.0-rc4/source/tools/testing/selftests/bpf/test_progs); 2. [test_bpf](https://elixir.bootlin.com/linux/v7.0-rc4/source/lib/test_bpf.c))

## Install

Use opam to install coq (8.19.0) and coq-compcert. (*Coq is the old name of Rocq*)

```shell
opam switch create linux-ebpf --empty
opam pin coq 8.19.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-compcert yojson
```

## Build

The command `make` will build all Coq files.
```shell
make
```

## Semantics Validation

Two commands are provided to test two selftest suites.
```shell
make validation1 # build the workflow and test the execution trace from test_progs
make validation2 # build the workflow and test the execution trace from test_bpf
```

## Link to paper

```
.
├── semantics/
│       └── ebpfState.v -- eBPF State (Section 3.1)
│       └── ebpfSyntax.v -- eBPF State (Section 3.2, Fig 4)
│       └── ebpfBinSem.v -- eBPF semantics (Section 3.3, Fig 5-Fig 7) + Sequential Consistency Model (See Coq Section `eBPF_GlobalSem`)
│       └── main.ml -- The OCaml code for starting the validation workflow (Section 4.1, Fig. 8)
│       └── Validation.v -- Reference Interpreter (Section 4.2)
├── trace/
│       └── test_progs/ -- execution trace from the Linux eBPF selftest suite (Section 4.3)   
│       └── test_bpf/ -- execution trace from the Linux eBPF interpreter test suite (Section 4.3)
```

## Code Statistics

- Run the following command to get the lines of code

```shell
sudo apt-get install cloc

# Go to the root directory of this repo
make bpfcode # bpf semantic code size using coqwc
make validationcode # ocaml code size using cloc
```

Note that, we don't provide the kernel patch + eBPF observer code, and other files, it will be provided within a VM image during the AE.

- The code does not contain any unfinished proofs. To verify this, you can use the following command
```shell
# Go to the root directory of this repo
grep -r --include="*.v" "admit" .
```
