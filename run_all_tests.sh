#!/usr/bin/env bash

# Responds to environment variables:
#   * DOCKER
#   * STACKARGS
#   * PAR
#   * LLVM

# Hack, treat `./run_all_tests.sh -j` specially
if [ "$1" == "-j" ]; then
    PAR=1
elif [ "$1" == "" ]; then
    echo;
else
    echo "Unrecognized command line arg to run_all_tests.sh: $@";
    exit 1;
fi

PROCS=`getconf _NPROCESSORS_ONLN`
if [ "$PAR" == "1" ]; then
    MKPARARGS="-j${PROCS}"
    RACOPARARG="-j ${PROCS}"
else
    MKPARARGS=""
    RACOPARARG=""
fi

echo "Running full test suite, Parallelism flags = '$MKPARARGS' \n"
set -xe

cd `dirname $0`
top=`pwd`

hostname || echo "No hostname command, env says $HOSTNAME"
uname -a
which -a stack
which -a ghc
which -a racket
which -a gcc
stack --version | head
racket --version
gcc --version

# Set GIBBONDIR:
source set_env.sh

export PLTADDONDIR=`pwd`/.racket_sandbox/

# If we TRUST stack and racket, then leaving this out can speed up our incremental CI tests.
#echo "  Clean the working copy"
#echo "----------------------------------------"
# cd $top/; make clean

set +x; echo
echo "  Racket code (1/2)"
echo "----------------------------------------"
set -x

# First the core #lang implementation:
cd $top/; make racket


set +x; echo
echo "  Racket code (2/2)"
echo "----------------------------------------"
set -x

# Then misc other code/benchmarks:
cd $top/ASTBenchmarks/common/racket;         make $MKPARARGS
cd $top/ASTBenchmarks/substitution/treelang; make $MKPARARGS

raco make -v $RACOPARARG \
     $top/ASTBenchmarks/substitution/racket/subst.rkt \
     $top/ASTBenchmarks/rewrite.rkt

# racket $top/ASTBenchmarks/typecheck-stlc/examples.gib

# Run class compiler tests
# set +x; echo
# echo "  Class compiler tests"
# echo "----------------------------------------"
# cd $top/ASTBenchmarks/class-compiler; make test
# echo
# set -x

# If we wanted to be really aggressive we could run all racket files
# in the Repo:
# racket $top/ASTBenchmarks/tests/*.rkt


# [2016.11.08] {Having problems with this -RRN}
# raco make -v $top/kdTree-BenchMark/racket/*.rkt
racket $top/ASTBenchmarks/kdTree-BenchMark/racket/traversal.gib

STK="stack --allow-different-user"

if [ "$STACK_DOCKER" == "1" ]; then
    if [ "$COARSE_DOCKER" == "1" ]; then
        echo "ERROR: cannot use stack --docker when already running in COARSE_DOCKER=1"
        exit 1
    fi
    STK+=" --docker "

elif [ "$STACK_NIX" == "1" ]; then
    if [ "$COARSE_NIX" == "1" ]; then
        echo "ERROR: should not use stack --nix when already running in COARSE_NIX=1"
        exit 1
    fi
    STK+=" --nix "
fi

if [ "$COARSE_NIX" == "1" ]; then
    STK+=" --system-ghc "
else
    STK+=" --install-ghc "
fi

set +x; echo
echo "  Gibbon Compiler (1/2): build & unit tests"
echo "-------------------------------------------"
set -x
cd $top/gibbon-compiler
df -h

## See https://github.com/commercialhaskell/stack/issues/996 and
## https://github.com/iu-parfunc/gibbon/issues/108 for details.
TMP="$HOME/tmp/"
mkdir -p $TMP

if [ "$LLVM_ENABLED" == "1" ]; then
    echo "Building Gibbon with LLVM enabled"
    TMPDIR=$TMP $STK test --flag gibbon:llvm_enabled $STACKARGS $MKPARARGS
else
    TMPDIR=$TMP $STK test "$STACKARGS" $MKPARARGS
fi

echo "  Gibbon Compiler (2/2): compiler test suite"
echo "--------------------------------------------"

# Turning off -j for now [2016.11.06]
cd $top/gibbon-compiler
# make answers

## CSK: nix-shell sets an environment variable, SIZE=size. I've not been able
## track down what specific package (or something in our config) is responsible
## for this. I tried to write another minimal shell.nix script and that shell
## had this environment variable too.
##
## This leads to the "Prelude.read no parse" error that RRN reported in #108.
## Gibbon tries to parse "size" as an Int (in Gibbon.Common.getRunConfig) and
## that doesn't work out very well. Until we figure out the source of this
## rogue variable, we *unset* it here.
##
## [2019.02.15] Gibbon now uses qualified env vars (GIBBON_SIZE, GIBBON_...),
## but we still unset those here.
unset GIBBON_SIZE GIBBON_ITERS GIBBON_DEBUG

TMPDIR=$TMP $STK exec test-gibbon-examples -- -v2


# [2017.04.24] TEMP: Disabling below here while the compiler is under construction.
exit 0

if [ "$NOBINTREE" != "1" ]; then
    set +x; echo
    echo "  Bintree Microbench:"
    echo "----------------------------------------"
    set -x
    cd $top/BintreeBench
    if [ "$DOCKER" == "1" ]; then
        echo "Building under Docker, FULL benchmark set."
        make $MKPARARGS
        make run_small
    else
        echo "Not under Docker. Don't do a full Bintree build, it requires too many toolchains."
        make c ghc -j
        make run_small_core
    fi
fi


# [2017.01.11] Disabling for now.  Adds dependencies and we aren't using it:
# set +x; echo
# echo "  Handwritten Parser:"
# echo "----------------------------------------"
# set -x
# cd $top/deps/sexpr-1.3
# make || ./configure && make $MKPARARGS
# # TODO: Move to common:
# cd $top/ASTBenchmarks/common/c/
# make check
