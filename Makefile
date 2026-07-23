COQC := coqc
COQMAKEFILE := coq_makefile
COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

COQDIR := semantics
COQINCLUDES := -R $(COQDIR) bpf.ebpf

COQFILES := $(sort $(wildcard $(COQDIR)/*.v))

COQFILES_FILTERED := $(filter-out $(COQDIR)/Validation.v $(COQDIR)/Extraction.v,$(COQFILES))

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
	@rm -f $(COQDIR)/validation.ml $(COQDIR)/validation.mli

bpfcode:
	coqwc $(COQFILES_FILTERED)

validationcode:
	cloc $(COQDIR)/main.ml

validation: all
	cd $(COQDIR) && dune build

validation1: all
	cd $(COQDIR) && dune exec ./main.exe test_progs

validation2: all
	cd $(COQDIR) && dune exec ./main.exe test_bpf

distclean: clean
	@echo "Removing build system files..."
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf
