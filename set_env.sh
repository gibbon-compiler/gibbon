# This file must be sourced with ". set_env.sh" or "source set_env.sh"

if ! [ -d ./gibbon-compiler ]; then
    echo "Error: please source this handy set_env script from the directory that contains it.";
    return 1
fi

export GIBBONDIR=`pwd`
export GIBBON_NEWRTS_DIR=$GIBBONDIR/gibbon-rts
export PLTADDONDIR=$GIBBONDIR/.racket_sandbox/

STK="stack"
BUILD_ARGS=" --install-ghc build "

# A shortcut to make things easier:
function gib() {
    cur=`pwd`
    cd $GIBBONDIR/gibbon-compiler/
    $STK $BUILD_ARGS
    if [ "$?" == "0" ]; then
       # Version 1: find the executable, but execute natively:
       #   CMD=`$STK exec -- which gibbon`;
       #   cd $cur;
       #   $CMD $@;
       # Version 2: execute inside the environment:
       $STK exec -- bash -c "cd $cur && gibbon $*";
       cd $cur  
    else
        cd $cur;
        echo "'stack build' failed";
        return 1;
    fi
}

# A debugging version that prints back-traces upon exceptions.
#
# WARNING: as of stack 1.2 you need to stack-clean between using
# tc/tcd.  It is not smart enough to rebuild automatically and keep
# the build artifacts separate.
function gib_dbg() {
    BUILD_ARGS="$BUILD_ARGS --trace" gib $@
}

# Nix version
function gibn() {    
    STK="stack --nix" gib $@
}

function gibd() {
    # --docker-auto-pull isn't working:
    (cd $GIBBONDIR/gibbon-compiler/ && stack docker pull 2> /dev/null) && \
     STK="stack --docker " gib $@
}

# A quick verison that doesn't check for recompile.
function gibq() {    
    cur=`pwd`
    cd $GIBBONDIR/gibbon-compiler/
    CMD=`stack exec -- which gibbon`
    cd $cur
    $CMD $@
}
