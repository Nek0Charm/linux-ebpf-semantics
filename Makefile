COQC := coqc
COQMAKEFILE := coq_makefile
COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

COQDIRS := theories validator
GENERATED_DIR := validator
VALIDATOR_DIR := validator
COQINCLUDES := -R theories bpf.semantics -R validator bpf.validator

COQFILES := $(sort $(foreach d,$(COQDIRS),$(wildcard $(d)/*.v)))

COQFILES_FILTERED := $(filter-out $(VALIDATOR_DIR)/Validation.v $(VALIDATOR_DIR)/Extraction.v,$(COQFILES))

.PHONY: all clean distclean bpfcode validation validation1 validation2 validationcode

all: _CoqProject CoqMakefile
	@echo "Building project..."
	$(MAKE) -f CoqMakefile

_CoqProject: Makefile
	@echo "$(COQINCLUDES)" > $@

CoqMakefile: _CoqProject $(COQFILES) Makefile
	@echo "Generating build system..."
	$(COQMAKEFILE) -f $< $(COQFILES) $(COQEXTRAFLAGS) -o $@

clean:
	@echo "Cleaning build artifacts..."
	@if [ -f CoqMakefile ]; then make -f CoqMakefile clean; fi
	@if command -v dune >/dev/null 2>&1; then dune clean; fi
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf
	@find . \( \
		-name "*.vo" -o \
		-name "*.vok" -o \
		-name "*.vos" -o \
		-name "*.glob" -o \
		-name "*.aux" -o \
		-name "*.cmi" -o \
		-name "*.cmx" -o \
		-name "*.crashcoqide" \
	\) -exec rm -f {} +
	@rm -f $(GENERATED_DIR)/validation.ml $(GENERATED_DIR)/validation.mli

bpfcode:
	coqwc $(COQFILES_FILTERED)

validationcode:
	cloc $(VALIDATOR_DIR)/main.ml

validation: all
	dune build

validation1: all
	dune exec validator/main.exe -- --trace-root trace test_progs

validation2: all
	dune exec validator/main.exe -- --trace-root trace test_bpf

distclean: clean
	@echo "Removing build system files..."
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf
