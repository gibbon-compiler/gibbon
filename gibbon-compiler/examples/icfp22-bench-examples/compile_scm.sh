#!/usr/bin/env bash

for f in *.scm; do
    echo "(compile-program \"$f\")" | chez -q --optimize-level 3
done
