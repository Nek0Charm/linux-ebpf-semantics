# Formalizing the Linux eBPF Core ISA: A Mechanized Operational Semantics and Real-world Application

## Code Structure

- `theories/`: reusable Coq definitions and eBPF semantics
- `validator/`: Coq validation/extraction plus the handwritten OCaml CLI
- `trace/`: execution traces from Linux kernel + two official Linux eBPF test suites (1. [progs](https://elixir.bootlin.com/linux/v7.0-rc3/source/tools/testing/selftests/bpf/progs) / [test_progs](https://elixir.bootlin.com/linux/v7.0-rc3/source/tools/testing/selftests/bpf/test_progs); 2. [test_bpf](https://elixir.bootlin.com/linux/v7.0-rc3/source/lib/test_bpf.c))

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
├── theories/
│       └── ebpfState.v -- eBPF State (Section 3.1)
│       └── ebpfSyntax.v -- eBPF State (Section 3.2, Fig 4)
│       └── ebpfBinSem.v -- eBPF semantics (Section 3.3, Fig 5-Fig 7) + Sequential Consistency Model (See Coq Section `eBPF_GlobalSem`)
├── validator/
│       └── Extraction.v -- OCaml extraction entry point
│       └── Validation.v -- Reference Interpreter (Section 4.2)
│       └── validation.ml -- Generated OCaml (not tracked)
│       └── main.ml -- The OCaml CLI for the validation workflow (Section 4.1, Fig. 8)
└── trace/
        └── test_progs/ -- execution trace from the Linux eBPF selftest suite (Section 4.3)
        └── test_bpf/ -- execution trace from the Linux eBPF interpreter test suite (Section 4.3)
```

## Code Statistics

- Run the following command to get the lines of code

```shell
sudo apt-get install cloc

# Go to the root directory of this repo
make bpfcode # bpf semantic code size using coqwc
make validationcode # ocaml code size using cloc
```

The kernel patch and eBPF observer are provided in a separate Linux repository; its README gives their paths and execution instructions.
