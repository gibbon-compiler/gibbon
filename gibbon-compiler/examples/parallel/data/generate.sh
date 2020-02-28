#!/bin/bash

set -eo pipefail
set -x

PBBS_DIR="/u/ckoparka/chai/pbbs"

cd "$PBBS_DIR/nearestNeighbors/geometryData"
make

DATA_DIR="/u/ckoparka/chai/tree-velocity/gibbon-compiler/examples/parallel/data"
PLUMMER_DIR="$DATA_DIR/plummer"
UNIFORM_DIR="$DATA_DIR/uniform"

mkdir -p $PLUMMER_DIR
mkdir -p $UNIFORM_DIR

sizes=(50 100 200 400 800 1600 3200 6400 12800 25600 51200 100000 125000 150000 1000000 1048576 2097152 4194304 8388608 16777216 33554432)

for size in ${sizes[@]}; do
    filename="$PLUMMER_DIR/plummer_3d_$size.txt"
    ./plummer -d 3 "$size" "$filename"
    sed -i '1d' "$filename"

    filename="$UNIFORM_DIR/uniform_3d_$size.txt"
    ./plummer -d 3 "$size" "$filename"
    sed -i '1d' "$filename"
done
