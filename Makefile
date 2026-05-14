FSTAR_HOME ?= $(CURDIR)/fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

OUTPUT_DIR = _output

FSTAR_FLAGS = \
  --cache_checked_modules \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  --already_cached 'Prims FStar Pulse PulseCore'

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

ALL_SRC = $(wildcard *.fst)

.PHONY: verify clean

$(OUTPUT_DIR):
	@mkdir -p $@

.depend: $(ALL_SRC) | $(OUTPUT_DIR)
	$(FSTAR) --dep full $(ALL_SRC) --output_deps_to $@

-include .depend

verify: $(addsuffix .checked, $(ALL_SRC))
	@echo "=== all modules verified ==="

%.fst.checked: %.fst | $(OUTPUT_DIR)
	$(FSTAR) $<

clean:
	rm -rf $(OUTPUT_DIR) .depend
