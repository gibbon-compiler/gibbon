#!/bin/bash
# Compare two `snapc.sh` manifests.
#
# Prints one line per (program, config) whose generated C moved, plus a summary
# of how many compared identical.  An exit code of 1 means something changed.
#
# Usage: ./diffc.sh baseline.tsv new.tsv
set -u
BASE="${1:?usage: diffc.sh baseline.tsv new.tsv}"
NEW="${2:?usage: diffc.sh baseline.tsv new.tsv}"

LC_ALL=C join -t $'\t' -j 1 -o 0,1.2,1.3,2.2,2.3 \
  <(LC_ALL=C awk -F'\t' 'NR>1{print $1"\t"$2"\t"$3"\t"$4}' "$BASE" \
      | LC_ALL=C awk -F'\t' '{print $1"|"$2"\t"$3"\t"$4}' | LC_ALL=C sort) \
  <(LC_ALL=C awk -F'\t' 'NR>1{print $1"\t"$2"\t"$3"\t"$4}' "$NEW" \
      | LC_ALL=C awk -F'\t' '{print $1"|"$2"\t"$3"\t"$4}' | LC_ALL=C sort) \
  | LC_ALL=C awk -F'\t' '
      { total++
        if ($2 != $4) { rcmoved++; print "RC   " $1 "  " $2 " -> " $4 }
        else if ($3 != $5) { moved++; print "DIFF " $1 }
        else same++ }
      END { printf "compared %d  identical %d  changed %d  rc-changed %d\n", total, same, moved, rcmoved }'
