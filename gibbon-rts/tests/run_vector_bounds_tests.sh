#!/usr/bin/env bash
# VW-04 regression driver.
#
# Builds gibbon_rts.c together with vector_bounds_test.c in a PRIVATE temp
# directory with -D_GIBBON_BOUNDSCHECK, so it never touches gibbon-rts/build
# and can run alongside a compiler gate.  Two things are asserted:
#
#   1. the checked configuration COMPILES (it could not, until VW-04);
#   2. valid indices work and invalid ones are rejected deterministically,
#      each invalid case in its own process because the RTS exit(1)s.
#
# Usage: gibbon-rts/tests/run_vector_bounds_tests.sh [cc]
set -u
CC=${1:-gcc}
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
BIN=$TMP/vector_bounds_test
pass=0; fail=0

$CC -O1 -g -std=gnu11 -D_GIBBON_BOUNDSCHECK -D_GIBBON_VERBOSITY=1 \
    -D_GIBBON_GENGC=0 -D_GIBBON_EAGER_PROMOTION=1 -D_GIBBON_SIMPLE_WRITE_BARRIER=0 \
    -I "$ROOT/deps/uthash" -I "$ROOT/gibbon-rts/rts-c" -I "$ROOT/gibbon-rts/build" \
    -o "$BIN" "$ROOT/gibbon-rts/tests/vector_bounds_test.c" "$ROOT/gibbon-rts/rts-c/gibbon_rts.c" \
    -L "$ROOT/gibbon-rts/build" -Wl,-rpath,"$ROOT/gibbon-rts/build" -lgibbon_rts_ng -lm 2>"$TMP/cc.log"
if [ ! -x "$BIN" ]; then
  echo "FAIL: the -D_GIBBON_BOUNDSCHECK configuration does not compile with $CC"
  tail -20 "$TMP/cc.log"; exit 1
fi
echo "ok: -D_GIBBON_BOUNDSCHECK compiles with $CC"

expect_ok () { # case...
  if out=$("$BIN" "$@" 2>&1) && ! grep -q '^FAIL' <<<"$out"; then
    echo "  PASS  $* :: $out"; pass=$((pass+1))
  else
    echo "  FAIL  $* :: $out"; fail=$((fail+1))
  fi
}
expect_rejected () { # case...  must exit non-zero AND name the violation
  out=$("$BIN" "$@" 2>&1); rc=$?
  if [ $rc -ne 0 ] && grep -qE 'out of bounds|negative offset or length' <<<"$out"; then
    echo "  PASS  $* rejected :: $(tr -d '\n' <<<"$out")"; pass=$((pass+1))
  else
    echo "  FAIL  $* not rejected deterministically (rc=$rc) :: $(tr -d '\n' <<<"$out")"; fail=$((fail+1))
  fi
}

expect_ok valid
expect_ok generate
expect_ok slice
for n in 1 8 16 17 24 32; do
  expect_rejected bad-read   "$n" -1
  expect_rejected bad-read   "$n" "$n"
  expect_rejected bad-read   "$n" $((n+1))
  expect_rejected bad-update "$n" "$n"
done
expect_rejected bad-slice-index
expect_rejected negative-slice -1 3
expect_rejected negative-slice 0 -3

echo "vector bounds tests: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
