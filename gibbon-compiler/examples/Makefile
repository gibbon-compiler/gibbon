# =================================================================
# This Makefile contains several entrypoints for driving the tests.
# =================================================================

test: temporary
temporary: prebuild build
	$(MAKE) run_answers
	$(MAKE) run_tests_interp1
#	$(MAKE) run_tests_interp2
	$(MAKE) run_tests_pointer
	$(MAKE) run_tests_packed

default:
	rm -f *.err $(BLD)/*.err
	$(MAKE) test

# Our default testing entrypoint.
old_test:
	$(MAKE) smalltest
	@echo
	@echo "For extra assurance, running valgrind!"
	rm -f $(BLD)/*.valgrind
	$(MAKE) valgrind
	$(MAKE) valgrind_packed


ALL_TESTS= $(shell ls test*.gib)

# Temporary output dir:
BLD=./build_tmp

ANSWERS= $(addprefix $(BLD)/,$(ALL_TESTS:.gib=.ans))


# Number of processors:
# Here's a hacky way to try several things until one works.
PROCS = $(shell getconf _NPROCESSORS_ONLN || \
                nproc || \
                stack exec -- ghc -e GHC.Conc.getNumProcessors || \
                python -c 'import multiprocessing as m; print m.cpu_count()' )
# On Mac: "sysctl -n hw.ncpu" also "getconf _NPROCESSORS_ONLN" works
# On Windows?

# DEBUG=1 is currently where we start turning on the pass-by-pass interpreter.
DEBUG ?= 1
GIBBON= DEBUG=$(DEBUG) stack exec -- gibbon

GIBBONEXEC=$(shell stack exec -- which gibbon)

# Run the most important tests while still going quickly.
smalltest: prebuild build
	$(MAKE) benchtest
# Having weird trouble with race conditons on answers:
	$(MAKE) run_answers
	wc -l $(ANSWERS)
	@echo
	@echo "Answers available, now proceeding..."
# [2017.01.11] Fairly obsolete:
#	$(MAKE) parse_all
	$(MAKE) core_tests

# Test the benchmarking mode
benchtest: test24_input.gpkd
	@echo "\n Testing Gibbon's benchmarking mode."
	@echo "--------------------------------------------------"

	$(GIBBON) --bench-fun pass --bench-print test24_defs.gib
	@echo
	./test24_defs.exe --bench-input test24_input.gpkd  10 10
	@echo "Same benchmark, but in one command:"
	$(GIBBON) -b pass --bench-print --bench-input test24_input.gpkd  test24_defs.gib
	@echo
	@echo "\nNow with the full Racket Core grammar:"
	$(GIBBON) --bench-fun foo --bench-print --bench-input test25b_input.gpkd test25b_racketcore.gib
# Printing doesn't work yet:
	@echo "\nNow in packed mode:"
	$(GIBBON) --packed --bench-fun pass --bench-input test24_input.gpkd test24_defs.gib
	$(GIBBON) --packed --bench-fun foo --bench-print --bench-input test25b_input.gpkd test25b_racketcore.gib

# Testing on larger inputs.
# ================================================================================
BIG= $(TREELANGDIR)/ASTBenchmarks/cleaned_racket/share/pkgs/typed-racket-more/typed/private/framework-types.rkt.out.sexp
BIGPKD= $(TREELANGDIR)/ASTBenchmarks/binary_racket/share/pkgs/typed-racket-more/typed/private/framework-types.rkt.out.gpkd
PERF= perf stat -e cycles,instructions,cache-references,cache-misses,bus-cycles

ITERS=100

# Run on a single biggish file:
big: bigfold bigmap
bigfold:
	ls -l $(BIG)
	ls -l $(BIGPKD)
	$(GIBBON) --pointer --bench-print --bench-fun countnodes -o test25f_pointer.exe --cfile=test25f_pointer.c test25f_countnodes.gib
	$(GIBBON) --packed  --bench-print --bench-fun countnodes -o test25f_packed.exe  --cfile=test25f_packed.c  test25f_countnodes.gib
	@echo "Pointer version"
	$(PERF) ./test25f_pointer.exe --bench-input $(BIGPKD) 0 1000
	@echo "Packed version"
	$(PERF) ./test25f_packed.exe --bench-input $(BIGPKD) 0 1000

# Don't print with this one.  It's too big. I verified by hand that it worked [2017.01.12].
bigmap:
	$(GIBBON) --pointer  --bench-fun treewalk -o test26a_pointer.exe --cfile=test26a_pointer.c test26a_treewalk.gib
	$(GIBBON) --packed   --bench-fun treewalk -o test26a_packed.exe  --cfile=test26a_packed.c  test26a_treewalk.gib
	$(GIBBON) --pointer --bumpalloc --bench-fun treewalk -o test26a_pointer_bumpalloc.exe --cfile=test26a_pointer_bumpalloc.c test26a_treewalk.gib
	DEBUG=2 stack exec -- gibbon --optc="-g -DDEBUG" --pointer --bumpalloc --bench-fun treewalk -o test26a_pointer_bumpalloc_dbg.exe --cfile=test26a_pointer_bumpalloc.c test26a_treewalk.gib

	@echo; echo "Packed version"
	@echo "============================================================"
	$(PERF) ./test26a_packed.exe --bench-input $(BIGPKD) 0 $(ITERS)

	@echo; echo "Pointer version"
	@echo "============================================================"
	$(PERF) ./test26a_pointer.exe --bench-input $(BIGPKD) 0 $(ITERS)

	@echo; echo "Bumpalloc pointer version"
	@echo "============================================================"
	$(PERF) ./test26a_pointer_bumpalloc.exe --bench-input $(BIGPKD) 0 $(ITERS)

megamap:
	$(MAKE) BIGPKD=$(TREELANGDIR)/ASTBenchmarks/mega_asts/mega1_1.gpkd bigmap

# Less than 1K
# SMALL=./share/pkgs/htdp-lib/2htdp/planetcute/roof-north-east.rkt.out.gpkd
# exactly 4096 bytes:
SMALL=./share/pkgs/web-server-doc/web-server/scribblings/tutorial/examples/iteration-10.rkt.out.gpkd
minimap:
	du -sch $(TREELANGDIR)/ASTBenchmarks/binary_racket/$(SMALL)
	$(MAKE) BIGPKD=$(TREELANGDIR)/ASTBenchmarks/binary_racket/$(SMALL) ITERS=100000 bigmap
# ================================================================================

# Run all small examples / system tests.
# Assumes answers and build already available:
core_tests:
	$(MAKE) run_tests
	$(MAKE) run_tests_packed
	$(MAKE) run_tests_interp1
	$(MAKE) run_tests_interp2
ifeq ($(LLVM_ENABLED),1)
	@echo "Running LLVM tests ..."
	$(MAKE) run_tests_llvm
else
endif

#	$(MAKE) racket_valid
# Need methodology for this.
#	$(MAKE) racket_invalid

# Set to the name of a single test you'd like to test:
ONE=test00_add.gib
one:
	$(MAKE) $(BLD)/$(ONE:.gib=.ans)
	$(MAKE) $(BLD)/$(ONE:.gib=.intrp1.out)   EXTRA_SUFFIX=".intrp1"
	$(MAKE)                                   EXTRA_SUFFIX=".ptr" $(BLD)/$(ONE:.gib=.ptr.out)
	$(MAKE) FAILING_TESTS="$(PACKED_FAILING)" EXTRA_SUFFIX=".pkd" $(BLD)/$(ONE:.gib=.pkd.out)
#	$(MAKE) $(BLD)/$(ONE).interp2.out


BACKEND="C"
EXTRA_SUFFIX ?= .ptr
# How far to compile, --toC, --exe, --run:
RUN_MODE     ?= --run
# Additional args besides RUN_MODE:
GIBBONARGS ?= --optc=-g

TREELANGDIR ?= ../../
SANDBOXDIR= $(TREELANGDIR)/.racket_sandbox/

RUNRACKET= racket -A $(SANDBOXDIR)

# Not necessary, because we build each module before we run it:
prebuild: $(BLD) test24_input.gpkd
# [2017.01.12] It's probably good enough to build ONE test, which builds upstream stuff:
	PLTADDONDIR=$(SANDBOXDIR) raco make -j $(PROCS) -v test00_add.gib

$(BLD):
	mkdir -p $(BLD)

test24_input.gpkd: test24_input.dat test24_packit.rkt test24_defs.gib
	$(RUNRACKET) test24_packit.rkt

#----------------------------------------
# Test direct Racket execution:
#----------------------------------------
racket_valid: treelang_lib
	@echo "\nGenerating canonical answers from Racket:"
	@echo "-----------------------------------------"
	for f in `ls test*.gib`; do $(RUNRACKET) $$f | tee $$f.ans; done

racket_invalid: treelang_lib
	for f in `find ./error/ -name '*.gib'`; do $(RUNRACKET) $$f | tee $$f.ans; done

# ----------------------------------------

# --no-system-ghc
STK=stack --no-nix --no-docker

# Make sure the compiler is built, currently this builds it without nix/docker:
build:
ifeq ($(LLVM_ENABLED),1)
	$(STK) build --flag gibbon:llvm_enabled
else
	$(STK) build
endif

parse_all: build
	@echo "\n Parsing all tests, even those that don't run yet."
	@echo "--------------------------------------------------"
	rm -f *.parsed
	$(MAKE) all_parsed


all_parsed:  $(ALL_TESTS:.gib=.parsed)

%.parsed : %.gib
#	@echo "Parsing $<"
	$(GIBBON) --parse $< 2> $@

# Failing tests for the pointer-based C backend (default):
FAILING_TESTS ?= \
  test15b_symappend.gib \
  test16_forlist.gib test17_forfold.gib \
  test28_copyprop.gib \
  test25a_withprint.gib \
  test27b_subst.gib

# test25a, test27b - works except needs proper SYMBOL PRINTING

# NOTE:
# test11d_funrec.gib -- is giving the WRONG ANSWER
# test11f_funrec.gib -- ''

PASSING_TESTS = $(filter-out $(FAILING_TESTS),$(ALL_TESTS))

OUT_FILES=$(addprefix $(BLD)/,$(PASSING_TESTS:.gib=$(EXTRA_SUFFIX).out))
EXE_FILES=$(addprefix $(BLD)/,$(PASSING_TESTS:.gib=$(EXTRA_SUFFIX).exe))

# Run the tests that work.  Assumes "build" has already executed.
run_tests: $(BLD)
	@echo "\n Compiling and running tests through our compiler ($(EXTRA_SUFFIX)):"
	@echo "------------------------------------------------------------------"
	@echo "Running test set: "$(PASSING_TESTS)
#	@echo "\nFirst clear output files:"
#	rm -f $(OUT_FILES) 
	@echo ""
	$(MAKE) all_tests

all_tests: $(BLD) answers $(OUT_FILES)

# Assumes stack build. Builds AND RUNS all the tests:
# Take care to not collide between different EXTRA_SUFFIX modes.
#
# Depend on GIBBONEXEC so we retest when the binary changes.
build_tmp/%$(EXTRA_SUFFIX).out : %.gib $(GIBBONEXEC)
ifeq ($(RUN_MODE),--run)
	@$(MAKE) --no-print-directory $(@:.out=.exe)
	./$(@:.out=.exe) > $@ || ./err.sh $(@:.out=)
else
ifeq ($(BACKEND),LLVM)
	$(GIBBON) $(RUN_MODE) $(GIBBONARGS) --cfile=$(@:.out=.ll) --exefile=$(@:.out=.exe) $< > $@ || ./err.sh $(@:.out=)
else
	$(GIBBON) $(RUN_MODE) $(GIBBONARGS) --cfile=$(@:.out=.c) --exefile=$(@:.out=.exe) $< > $@ || ./err.sh $(@:.out=)
endif
endif
	@./diff.sh $(BLD)/$(basename $<).ans $@ || ./err.sh $(@:.out=)

# Just build the tests
build_tests: $(EXE_FILES)

build_tmp/%$(EXTRA_SUFFIX).exe : %.gib $(GIBBONEXEC)
ifeq ($(BACKEND),LLVM)
	$(GIBBON) --run $(GIBBONARGS) $< --cfile=$(@:.exe=.ll) --exefile=$@ || ./err.sh $(BLD)/$(basename $<)$(EXTRA_SUFFIX)
else
	$(GIBBON) --run $(GIBBONARGS) $< --cfile=$(@:.exe=.c) --exefile=$@ || ./err.sh $(BLD)/$(basename $<)$(EXTRA_SUFFIX)
endif

PACKED_FAILING ?= \
 test00d_printData.gib test00e_func.gib test02d_printPair.gib test02e_printNest.gib test04c_ifvector.gib \
 test04d_vecfun.gib test05c_arity2.gib \
 test06a_two_cases.gib test06b_case.gib test06c_nested.gib \
 test06d_rec.gib test06e_rec.gib test06f_rec.gib test06g_rec.gib test06h_rec.gib test06i_casecase.gib \
 test08_dict.gib test08b_dict.gib test08c_dict.gib test08d_sharedict.gib \
 test10_desugar.gib test10b_desugar.gib \
 test11c_funrec.gib test11d_funrec.gib test11e_funrec.gib test11f_funrec.gib \
 test12b_traverse.gib test12c_traverse.gib \
 test15b_symappend.gib \
 test12_skip.gib test16_forlist.gib test17_forfold.gib \
 test18_badconstraint.gib test18b_tupconstraint.gib test18c_identity1.gib test18d_identity2.gib \
 test18e_identity3.gib test18f_flip.gib test18g_identity4.gib \
 test20a_withprint.gib test20b_bintree.gib test20g_bintree.gib test20h_bintree.gib \
 test24_defs.gib \
 test25a_withprint.gib test25d_racketcore.gib test25f_countnodes.gib \
 test26a_treewalk.gib test26_treewalk.gib \
 test27a_subst.gib test27b_subst.gib test27c_subst.gib \
 test28_copyprop.gib \
 test_add1.gib test_addtrees.gib test_buildstree.gib test_buildtreesum.gib test_buildtwotrees.gib \
 test_rightmost.gib test_stree.gib test_sumstree.gib test_sumupseteven.gib

 # test12_skip.gib test16_forlist.gib test17_forfold.gib \
 # test18b_tupconstraint.gib test18f_flip.gib \
 # test20b_bintree.gib  \
 # test25a_withprint.gib \
 # test27a_subst.gib \
 # test27b_subst.gib test27c_subst.gib test28_copyprop.gib

# test20b_bintree.gib   -- requires copy insertion
# test12_skip.gib       -- requires copy insertion!! unbound var thru to C code
# test16_forlist.gib    -- requires lists. No lists yet
# test17_forfold.gib    -- requires lists. No lists yet

# This is the default mode:
run_tests_pointer: run_tests

# Run the tests that work under the packed regime:
run_tests_packed: answers
	$(MAKE) run_tests RUN_MODE="--run" GIBBONARGS="$(GIBBONARGS) --packed" FAILING_TESTS="$(PACKED_FAILING)" EXTRA_SUFFIX=".pkd"

# This one is seriously rotted:
INTERP2_FAILING = \
  test16_forlist.gib test17_forfold.gib \
  test28_copyprop.gib \
  test25a_withprint.gib \
  test27b_subst.gib

# [2017.04.24] TEMP disabled:
#  test00a_size.gib test00b_printBool.gib test00d_printData.gib \
  test02d_printPair.gib test02e_printNest.gib test03d_eqs.gib \
  test04d_vecfun.gib \
  test06a_two_cases.gib test06b_case.gib test06_case.gib test06c_nested.gib \
  test06d_rec.gib test06e_rec.gib test06f_rec.gib test06g_rec.gib \
  test06h_rec.gib test06i_casecase.gib test07b_iterate.gib test11b_fundata.gib test11c_funrec.gib \
  test11d_funrec.gib test11e_funrec.gib test11f_funrec.gib  \
  test12b_traverse.gib test12c_traverse.gib test12_skip.gib \
  test16_forlist.gib test17_forfold.gib \
  test18_badconstraint.gib test18b_tupconstraint.gib \
  test18c_identity1.gib test18d_identity2.gib test18e_identity3.gib test18f_flip.gib test18g_identity4.gib \
  test20_bintree.gib \
  text08_dict.gib test08b_dict.gib test08c_dict.gib test08d_sharedict.gib \
  test13_build.gib test13b_build.gib  \
  test20a_withprint.gib test20b_bintree.gib test20c_bintree.gib test20d_bintree.gib test20e_bintree.gib \
  test20f_bintree.gib test20g_bintree.gib \
  test25a_withprint.gib test25b_racketcore.gib test25_rackcore.gib \
  test25c_racketcore.gib test25d_racketcore.gib test25e_countnodes.gib test25f_countnodes.gib \
  test11_fundata.gib test10_desugar.gib test10b_desugar.gib test24_defs.gib \
  test09_recur.gib test08_dict.gib test02b_datacon.gib test02c_case.gib \
  test26_treewalk.gib test26a_treewalk.gib test27a_subst.gib \
  test27b_subst.gib test27c_subst.gib test28_copyprop.gib

# Running through interpreter, no --packed/cursorize:
run_tests_interp2: answers
	$(MAKE) run_tests RUN_MODE="--interp2"  FAILING_TESTS="$(INTERP2_FAILING)" EXTRA_SUFFIX=".intrp2"


# Populated [2016.12.10]
INTERP1_FAILING = test16_forlist.gib test17_forfold.gib test25b_racketcore.gib \
  test25a_withprint.gib test27b_subst.gib test27c_subst.gib test28_copyprop.gib


run_tests_interp1: answers
	$(MAKE) run_tests RUN_MODE="--interp1"  FAILING_TESTS="$(INTERP1_FAILING)" EXTRA_SUFFIX=".intrp1"


# --------------------------------------------------------------------------------

build_tmp/%.ans : %.gib
# Optional, could prebuild before running:
#	raco make -v $<
	$(RUNRACKET) $< > $@ || rm -f $@
#	$(RUNRACKET) $< | tee $@

run_answers:
	@echo "\nGenerating canonical answers from Racket:"
	@echo "-----------------------------------------"
	$(MAKE) answers

answers: $(ANSWERS)

# Run tests through the LLVM backend

build_gibbon_llvm_lib:
	clang -std=gnu11 -c -fno-exceptions -fPIC $(TREELANGDIR)/gibbon-compiler/lib.c

LLVM_PASSING_TESTS = test00_add.gib test00a_size.gib test00b_printBool.gib \
  test00c_printBool.gib test00d_printData.gib test00e_func.gib \
  test01_if.gib test01b_ifif.gib \
  test02_arith.gib test02b_datacon.gib test02c_case.gib test02d_printPair.gib \
  test03_let.gib test03b_eqs.gib test03d_eqs.gib \
  test04_vector.gib test04b_vector.gib test04c_ifvector.gib \
  test05_app.gib test05b_app.gib test05c_arity2.gib \
  test06_case.gib test06a_two_cases.gib test06b_case.gib test06c_nested.gib test06d_rec.gib test06e_rec.gib test06f_rec.gib test06g_rec.gib test06h_rec.gib test06i_casecase.gib \
  test07_time.gib test07b_iterate.gib \
  test08_dict.gib test08b_dict.gib test08c_dict.gib test08d_sharedict.gib \
  test10_desugar.gib \
  test11_fundata.gib test11b_fundata.gib test11c_funrec.gib test11d_funrec.gib test11e_funrec.gib test11f_funrec.gib \
  test12_skip.gib test12b_traverse.gib test12c_traverse.gib \
  test13_build.gib test13b_build.gib \
  test19_unarytree.gib \
  test20_bintree.gib test20c_bintree.gib test20d_bintree.gib test20f_bintree.gib test20g_bintree.gib \
  test24_defs.gib \
  test25e_countnodes.gib

LLVM_FAILING_TESTS = test02e_printNest.gib \
  test10b_desugar.gib \
  test20a_withprint.gib test20b_bintree.gib test20e_bintree.gib \
  test25_rackcore.gib test25a_withprint.gib test25b_racketcore.gib test25c_racketcore.gib test25d_racketcore.gib test25f_countnodes.gib \
  test26_treewalk.gib test26a_treewalk.gib \
  test27a_subst.gib test27b_subst.gib test27c_subst.gib test28_copyprop.gib

# test16_forlist.gib test17_forfold.gib

run_tests_llvm: answers build_gibbon_llvm_lib
	$(MAKE) run_tests PASSING_TESTS="$(LLVM_PASSING_TESTS)" GIBBONARGS="--llvm" EXTRA_SUFFIX="_llvm" BACKEND="LLVM"


# Valgrind should be part of our regression testing:
# --------------------------------------------------------------------------------

# Not assuming Valgrind for OSX atm:
OS := $(shell uname)

ifeq ($(OS),Darwin)
 VALGRIND_CMD := @echo "Not running valgrind on this: "
else
 VALGRIND_CMD := valgrind -q --error-exitcode=99
endif

valgrind_packed:
	$(MAKE) run_valgrind GIBBONARGS="--packed --optc=-g " FAILING_TESTS="$(PACKED_FAILING)" EXTRA_SUFFIX=".pkd"; \

# if test `uname` == "Linux" ; then \
        #   $(MAKE) run_valgrind GIBBONARGS="--packed --optc=-g " FAILING_TESTS="$(PACKED_FAILING)" EXTRA_SUFFIX=".pkd"; \
        # else echo "Only supporting valgrind on linux."; fi

valgrind:
	$(MAKE) run_valgrind GIBBONARGS=" --optc=-g " EXTRA_SUFFIX=".ptr" 


VALGRIND_FILES=$(addprefix $(BLD)/,$(PASSING_TESTS:.gib=$(EXTRA_SUFFIX).valgrind))

run_valgrind: $(VALGRIND_FILES)

build_tmp/%$(EXTRA_SUFFIX).valgrind : %.gib build_tmp/%$(EXTRA_SUFFIX).exe
#	@echo "\n Valgrind, testing $(basename $(basename $@))"
#	@echo "--------------------------------------------------"
	$(VALGRIND_CMD) $(basename $@).exe
	@touch $@

# --------------------------------------------------------------------------------

# Build the Racket library-based implementation of #lang gibbon.
treelang_lib:
	raco make -v ../../gibbon/main.rkt 

RMINTERMEDIATE = rm -rf *.exe *.o *.c  *.out *.err *.valgrind *.parsed *.intrp* *.exe.dSYM

clean:
	$(RMINTERMEDIATE)
	(cd $(BLD); $(RMINTERMEDIATE) )
	rm -rf test24_input.gpkd ./compiled 
	(cd error/; rm -f *.exe *.o *.c  *.out *.err *.valgrind *.parsed)

distclean: clean
	rm -f *.ans
	cd error/; rm -f *.ans

.PHONY: default test valgrind_packed valgrind run_valgrind
.PHONY: prebuild build run_racket treelang_lib answers run_tests core_tests big
.PHONY: run_tests_interp2 run_tests_packed clean distclean benchtest
