#!/usr/bin/env bash
# VW-09: direct RTS scalar-count footer tests.  Builds gibbon_rts.c together
# with the test into a PRIVATE temp dir, so gibbon-rts/build is never touched
# and this can run alongside a compiler gate.
set -u
CC=${1:-gcc}
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
BIN=$TMP/scalar_count_footer_test
$CC -O1 -g -std=gnu11 -D_GIBBON_VERBOSITY=1 -D_GIBBON_GENGC=0 \
    -D_GIBBON_EAGER_PROMOTION=1 -D_GIBBON_SIMPLE_WRITE_BARRIER=0 \
    -I "$ROOT/deps/uthash" -I "$ROOT/gibbon-rts/rts-c" -I "$ROOT/gibbon-rts/build" \
    -o "$BIN" "$ROOT/gibbon-rts/tests/scalar_count_footer_test.c" \
    "$ROOT/gibbon-rts/rts-c/gibbon_rts.c" \
    -L "$ROOT/gibbon-rts/build" -Wl,-rpath,"$ROOT/gibbon-rts/build" \
    -lgibbon_rts_ng -lm 2>"$TMP/cc.log"
if [ ! -x "$BIN" ]; then echo "FAIL: build with $CC"; tail -20 "$TMP/cc.log"; exit 1; fi
echo "built with $CC"
"$BIN"
