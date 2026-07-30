COQMAKEFILE := CoqMakefile

.PHONY: all clean coqchk admitted-check axiom-check inventory check

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean:
	-$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

coqchk: all
	$(MAKE) -f $(COQMAKEFILE) validate

admitted-check:
	@if grep -rn "Admitted\." rocq/*.v; then \
	  echo "ERROR: Admitted found (see above)."; exit 1; \
	else \
	  echo "No Admitted statements found."; \
	fi

axiom-check:
	@if grep -rEn "^(Axiom|Parameter|Conjecture)\b" rocq/*.v; then \
	  echo "ERROR: project-defined Axiom/Parameter/Conjecture found (see above)."; exit 1; \
	else \
	  echo "No project-defined axioms, parameters, or conjectures found."; \
	fi

inventory:
	./scripts/check_inventory.sh

check: admitted-check axiom-check all coqchk inventory
	@echo "All Phase 1 checks passed."
