GIBBONDIR ?= ../

SANDBOXDIR= $(GIBBONDIR)/.racket_sandbox/

RUNRACKET= racket -A $(SANDBOXDIR)

RUNGHC= ghc

#----------------------------------------
# Generate answers from Racket
#----------------------------------------

GIB_EXAMPLES_DIR=./examples

# Temporary output dir:
GIB_BLD=$(GIB_EXAMPLES_DIR)/build_tmp

GIB_TESTS= $(shell ls $(GIB_EXAMPLES_DIR)/*.gib)

GIB_ANSWERS= $(addprefix $(GIB_BLD)/,$(notdir $(addsuffix .ans,$(GIB_TESTS))))

examples/build_tmp/%.gib.ans : $(GIB_EXAMPLES_DIR)/%.gib
	$(RUNRACKET) $< > $@ || rm -f $@

#----------------------------------------
# Generate answers from GHC
#----------------------------------------

HS_EXAMPLES_DIR=./examples/hs

HS_TESTS= $(shell ls $(HS_EXAMPLES_DIR)/*.hs)

HS_ANSWERS= $(addprefix $(GIB_BLD)/,$(notdir $(addsuffix .ans,$(HS_TESTS))))

examples/build_tmp/%.hs.ans : $(HS_EXAMPLES_DIR)/%.hs
	cp $< $(GIB_BLD)
	name=$(basename $(notdir $<))
	$(RUNGHC) $< -main-is $(basename $(notdir $<))
	$(HS_EXAMPLES_DIR)/$(basename $(notdir $<)) > $@ || rm -f $@

#----------------------------------------

run_answers:
	@echo "\nGenerating canonical answers from Racket:"
	@echo "-----------------------------------------"
	$(MAKE) answers

answers: $(GIB_ANSWERS) $(HS_ANSWERS)

.PHONY: answers debug
