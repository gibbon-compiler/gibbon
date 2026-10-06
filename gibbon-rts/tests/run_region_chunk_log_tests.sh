#!/usr/bin/env bash
# Region chunk log: direct RTS tests.  Builds gibbon_rts.c together with the
# test into a PRIVATE temp dir, so gibbon-rts/build is never touched and this
# can run alongside a compiler gate.
#
# Runs BOTH ways: with the feature on (the real tests) and with it off (the
# stubs must still link, because generated code calls them unconditionally).
set -u
CC=${1:-gcc}
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
rc=0
for RR in 1 0; do
  BIN=$TMP/region_chunk_log_test_$RR
  $CC -O1 -g -std=gnu11 -D_GIBBON_VERBOSITY=1 -D_GIBBON_GENGC=0 \
      -D_GIBBON_EAGER_PROMOTION=1 -D_GIBBON_SIMPLE_WRITE_BARRIER=0 \
      -D_GIBBON_REGIONRESET=$RR \
      -I "$ROOT/deps/uthash" -I "$ROOT/gibbon-rts/rts-c" -I "$ROOT/gibbon-rts/build" \
      -o "$BIN" "$ROOT/gibbon-rts/tests/region_chunk_log_test.c" \
      "$ROOT/gibbon-rts/rts-c/gibbon_rts.c" \
      -L "$ROOT/gibbon-rts/build" -Wl,-rpath,"$ROOT/gibbon-rts/build" \
      -lgibbon_rts_ng -lm 2>"$TMP/cc.log"
  if [ ! -x "$BIN" ]; then
    echo "FAIL: build with $CC at _GIBBON_REGIONRESET=$RR"; tail -20 "$TMP/cc.log"; exit 1
  fi
  echo "built with $CC (_GIBBON_REGIONRESET=$RR)"
  "$BIN" || rc=1
done
exit $rc
