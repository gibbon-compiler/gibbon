#!/bin/bash
# The --mpl backend must emit SML that MLton accepts, and the resulting
# executable must print what the C backend prints.
#
# The compiled --pointer binary is the oracle: it is what every recorded result
# in this project was produced with.  Timing lines are stripped because the SML
# backend does not emit them.
#
# Usage: run_mpl_backend_tests.sh [path-to-gibbon]
set -u

GIBBON=${1:-}
if [ -z "$GIBBON" ]; then
  GIBBON=$(command -v gibbon)
fi
if [ ! -x "$GIBBON" ]; then
  echo "run_mpl_backend_tests.sh: no gibbon executable (pass one as \$1)" >&2
  exit 2
fi
if ! command -v mlton > /dev/null; then
  echo "run_mpl_backend_tests.sh: mlton not installed; skipping" >&2
  exit 0
fi

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
export GIBBONDIR=$ROOT
SRCDIR=$HERE/mpl
WD=$(mktemp -d)
trap 'rm -rf "$WD"' EXIT

pass=0; fail=0

strip_timing () {
  grep -vE '^(ITER TIMES|ITERS|SIZE|BATCHTIME|SELFTIMED):?'
}

# A program whose --mpl output must compile, run, and match --pointer.
check_matches () {
  local src="$1" b
  b=$(basename "$src" .hs)
  cp "$src" "$WD/$b.hs"
  ( cd "$WD" && ulimit -v 8388608
    "$GIBBON" --pointer --to-exe -o "$b.exe" "$b.hs" ) > "$WD/$b.c.log" 2>&1
  if [ ! -x "$WD/$b.exe" ]; then
    fail=$((fail+1)); echo "  FAIL  $b (the --pointer oracle does not build)"; return
  fi
  local want got
  want=$( cd "$WD" && ulimit -v 8388608; timeout 600 "./$b.exe" 2>/dev/null | strip_timing )
  # --mpl-exe rather than --mpl-run, so MLton's own diagnostics stay out of the
  # program's output.
  ( cd "$WD" && ulimit -v 8388608
    "$GIBBON" --mpl-exe "$b.hs" ) > "$WD/$b.sml.log" 2>&1
  if [ ! -x "$WD/$b" ]; then
    fail=$((fail+1)); echo "  FAIL  $b (MLton rejected the emitted SML)"
    sed -n '1,6p' "$WD/$b.sml.log" | sed 's/^/          /'
    return
  fi
  got=$( cd "$WD" && ulimit -v 8388608; timeout 600 "./$b" 2>/dev/null | strip_timing )
  if [ "$want" = "$got" ]; then
    pass=$((pass+1)); echo "  PASS  $b"
  else
    fail=$((fail+1)); echo "  FAIL  $b (output differs)"
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | sed 's/^/          /'
  fi
}

# A program the backend cannot honestly compile must say so and stop, rather
# than emit SML that MLton rejects or that computes at the wrong width.
check_rejected () {
  local src="$1" want="$2" b out
  b=$(basename "$src" .hs)
  cp "$src" "$WD/$b.hs"
  out=$( cd "$WD" && ulimit -v 8388608; "$GIBBON" --mpl "$b.hs" 2>&1 )
  if printf '%s' "$out" | grep -q "$want"; then
    pass=$((pass+1)); echo "  PASS  $b (rejected: $want)"
  else
    fail=$((fail+1)); echo "  FAIL  $b (expected a rejection mentioning '$want')"
    printf '%s\n' "$out" | sed -n '1,4p' | sed 's/^/          /'
  fi
}

echo "--mpl backend:"
for f in "$SRCDIR"/*.hs; do
  check_matches "$f"
done

AOS=$ROOT/gibbon-compiler/examples/soa_examples/programs/AOS
if [ -d "$AOS" ]; then
  # Real corpus programs: packed datatypes, recursion, tuple returns.
  check_matches "$AOS/MonoTree.hs"
  check_matches "$AOS/KDTree.hs"
  # Narrow widths have no SML equivalent; the backend must say so.
  check_rejected "$AOS/ArithConstFold.hs" "not supported by the SML backend"
  check_rejected "$AOS/ExplicitConversions.hs" "not supported by the SML backend"
fi

echo "mpl-backend: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
