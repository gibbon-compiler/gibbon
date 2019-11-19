#!/bin/bash
set -e
set -o pipefail

depths=(1 2 4 8 16)

for d in "${depths[@]}"
do
    racket gen-lc.rkt $d ast_$d.sexp ast_$d.gpkd
    echo "Wrote ast_$d.sexp ast_$d.gpkd"
done
