TREELANGDIR ?= ../

SANDBOXDIR= $(TREELANGDIR)/.racket_sandbox/

RUNRACKET= racket -A $(SANDBOXDIR)

#----------------------------------------
# Generate answers from Racket
#----------------------------------------

EXAMPLES_DIR=./examples

ALL_TESTS= $(shell ls $(EXAMPLES_DIR)/*.gib)

# Temporary output dir:
BLD=$(EXAMPLES_DIR)/build_tmp

ANSWERS= $(addprefix $(BLD)/,$(notdir $(ALL_TESTS:.gib=.ans)))

examples/build_tmp/%.ans : $(EXAMPLES_DIR)/%.gib
	$(RUNRACKET) $< > $@ || rm -f $@

run_answers:
	@echo "\nGenerating canonical answers from Racket:"
	@echo "-----------------------------------------"
	$(MAKE) answers

answers: $(ANSWERS)

.PHONY: answers
