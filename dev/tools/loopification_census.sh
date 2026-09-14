#!/bin/bash
# Loopification census (2026-09-12 audit remediation, Phase 0.3).
#
# For every program in the audit reproducer corpus, records whether the AoS
# flat loopify pass (LoopifyFlatTraversals) and/or the SoA loopify pass
# (LoopifyTraversals) rewrote it, under three configurations: no loopification
# flag ("base"), --opt-loopification ("loop"), and
# --opt-loopification --auto-loopification ("auto").
#
# AoS marker: `while (*X != *Y)` -- LoopifyFlatTraversals.hs is the sole
#   producer of the WhileCursorEnd construct this compiles to (verified by
#   grepping every constructor site in gibbon-compiler/src/Gibbon).
# SoA marker: the substring `count_footer_loc` -- a name LoopifyTraversals.hs
#   alone mints, for the outer per-buffer chunk loop.
#
# Usage: GIBBON_CORPUS_DIR=/path/to/corpus GIBBON_EXE=/path/to/gibbon-exe \
#          ./census.sh > census_out/census.csv
set -u
CORPUS="${GIBBON_CORPUS_DIR:-/workdisk/git/gibbon-audit-2026-09-12}"
GEXE="${GIBBON_EXE:?set GIBBON_EXE to a serialised (flock-wrapped) gibbon invocation}"
OUT="${GIBBON_CENSUS_OUT:-./census_out}"
export GIBBONDIR="${GIBBONDIR:-/workdisk/git/gibbon}"
mkdir -p "$OUT/aos" "$OUT/soa"
echo "area,file,kind,loopified_flag,ok,aos_hits,soa_hits"

compile_one () {
  local src="$1" area="$2" kind="$3" flagname="$4"; shift 4
  local base cfile
  base=$(basename "$src" .hs)
  cfile="$OUT/$kind/${area}_${base}_${flagname}.c"
  ( ulimit -v 8388608
    cd "$(dirname "$src")" && "$GEXE" --packed --use-mutable-cursors --no-ran "$@" --toC --cfile "$cfile" "$(basename "$src")" ) \
    > "$cfile.log" 2>&1
  local rc=$?
  local aos=0 soa=0
  if [ -f "$cfile" ]; then
    aos=$(grep -cE 'while \(\*[A-Za-z0-9_]+ != \*[A-Za-z0-9_]+\)' "$cfile")
    soa=$(grep -c 'count_footer_loc' "$cfile")
  fi
  echo "$area,$base,$kind,$flagname,$rc,$aos,$soa"
}

# area3 = AoS flat loopify corpus
for f in "$CORPUS"/area3/*.hs; do
  bn=$(basename "$f")
  case "$bn" in *_e_loop.hs|*_e_noloop.hs|*_ea.hs) continue;; esac
  compile_one "$f" area3 aos base
  compile_one "$f" area3 aos loop --opt-loopification
  compile_one "$f" area3 aos auto --opt-loopification --auto-loopification
done

# area4 = SoA loopify corpus
for f in "$CORPUS"/area4/src/*.hs; do
  compile_one "$f" area4 soa base --store-scalar-field-counts
  compile_one "$f" area4 soa loop --store-scalar-field-counts --opt-loopification
  compile_one "$f" area4 soa auto --store-scalar-field-counts --opt-loopification --auto-loopification
done
