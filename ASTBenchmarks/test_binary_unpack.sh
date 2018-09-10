#!/bin/bash

echo "Testing that all binary files in ./binary_racket can unpack successfully."

set -xe

HERE=`pwd`
cd ../; source set_env.sh

cd $GIBBONDIR/gibbon-compiler/examples
tc --bench foo test25b_racketcore.sexp -o $HERE/unpack_test.exe

cd $HERE
for file in `find ./binary_racket -name "*.sexp"`; do
    ./unpack_test.exe --bench-input $file
done
