# Coq theories

The reusable semantics dependency chain is:

`ebpfSyntax` → `GlobalSem`/`ebpfState` → `ebpfDecoder`/`ebpfBinSem`.

The reference interpreter and extraction entry point live in `validator/` and
extend this chain as `Validation` → `Extraction`.

`Nondeterminism`, `CMemoryModel`, and `SCLanguage` are auxiliary modules for
the concurrency and interaction-semantics work. They are checked by the build,
but are not currently dependencies of the extracted validation executable.

This directory is the public Coq theory mapped to `bpf.semantics`. The
validation implementation is internal to the project and is mapped separately
from `validator/` to `bpf.validator`.
