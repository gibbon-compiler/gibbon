#!/bin/bash
# Generated-C byte snapshot over the audit reproducer corpus.
#
# Compiles every corpus program under five flag configurations and records one
# line per (program, config): the exit code and the SHA-256 of the emitted C.
# `diffc.sh` compares two such manifests.  A pass change that is meant to be a
# check rather than a rewrite must leave every hash alone.
#
# --toC touches no shared state (it never builds gibbon-rts), so the compiles
# run in parallel; anything reaching --to-exe must be serialised instead.
#
# Usage: GIBBON_EXE=/path/to/gibbon [GIBBON_CORPUS_DIR=...] [GIBBON_SNAP_OUT=...] \
#          ./snapc.sh > manifest.tsv
set -u
CORPUS="${GIBBON_CORPUS_DIR:-/workdisk/git/gibbon-audit-2026-09-12}"
GEXE="${GIBBON_EXE:?set GIBBON_EXE to a gibbon binary}"
OUT="${GIBBON_SNAP_OUT:?set GIBBON_SNAP_OUT to a directory for the emitted C}"
JOBS="${GIBBON_SNAP_JOBS:-8}"
export GIBBONDIR="${GIBBONDIR:-/workdisk/git/gibbon}"

BASE="--packed --use-mutable-cursors --no-ran"
declare -A CFG=(
  [base]="$BASE"
  [counts]="$BASE --store-scalar-field-counts"
  [loop]="$BASE --store-scalar-field-counts --opt-loopification"
  [auto]="$BASE --store-scalar-field-counts --opt-loopification --auto-loopification"
  [full]="$BASE --store-scalar-field-counts --opt-loopification --auto-loopification --opt-selective-buffer-sharing --opt-vectorization"
)

mkdir -p "$OUT"

compile_one () {
  local src="$1" cfgname="$2"; shift 2
  local rel key cfile rc hash
  local -a flags=("$@")
  rel="${src#"$CORPUS"/}"
  key="${rel//\//_}"; key="${key%.hs}"
  cfile="$OUT/${key}__${cfgname}.c"
  # `flags` is captured here because `$@` inside `run_one` would be run_one's
  # own (empty) argument list, not this function's.
  run_one () {
    ( ulimit -v 8388608
      cd "$(dirname "$src")" && "$GEXE" "${flags[@]}" --toC --cfile "$cfile" "$(basename "$src")" ) \
      > "$cfile.log" 2>&1
  }
  run_one
  rc=$?
  # A signal is memory pressure from the parallel fan-out, not a compiler
  # answer: GHC's RTS aborts with "strange closure type" under the -v cap.
  # Retry once so a flake cannot be read as a codegen change.
  if [ $rc -ge 128 ]; then run_one; rc=$?; fi
  if [ -s "$cfile" ]; then hash=$(sha256sum "$cfile" | cut -d' ' -f1); else hash="-"; fi
  printf '%s\t%s\t%s\t%s\n' "$rel" "$cfgname" "$rc" "$hash"
}
export -f compile_one
export CORPUS OUT GEXE GIBBONDIR

printf 'file\tconfig\trc\tsha256\n'
for name in base counts loop auto full; do
  find "$CORPUS" -name '*.hs' -print0 \
    | xargs -0 -P "$JOBS" -I{} bash -c 'compile_one "$1" "$2" $3' _ {} "$name" "${CFG[$name]}"
done | LC_ALL=C sort
