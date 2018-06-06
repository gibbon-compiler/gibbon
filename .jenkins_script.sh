#!/usr/bin/env bash

set -xe

echo "Running on machine: "`hostname -a || echo env says $HOSTNAME`
uname -a

echo "Git commit:"
(git log | head) || echo ok
echo "Git commit depth: "
(git log --pretty=oneline | wc -l) || echo ok

top=`pwd`

# This testing mode assumes that nix/docker integration is OFF by default:
export STACKARGS="--no-system-ghc"

if [ "$DOCKER" == "1" ]; then
    # Make bintree-bench image:
    cd $top/BintreeBench
    make docker

    # Make dependent image:
    cd $top/
    docker build -t tree-velocity .

elif [ "$USE_NIX" == "1" ]; then

    # Here by default we use a pinned version of the software ecosystem:
    nix-shell --pure --command  "USE_NIX=1 ./run_all_tests.sh $@"

else
    # HACK to get Jenkins to use proper Racket and GCC versions
    export PATH=/opt/gcc/5.3.0/bin/:$PATH
    export PATH=/u/crest-team/opt/bin:$PATH
    echo $PATH
    ./run_all_tests.sh $@
fi
