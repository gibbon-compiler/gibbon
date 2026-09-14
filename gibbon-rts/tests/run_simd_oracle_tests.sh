#!/usr/bin/env bash
# VW-13: differential tests of the SIMD helpers Gibbon EMITS against a
# two's-complement scalar reference.
#
#   simd_width_oracle_test.c  randomized, every width x {mul,add,sub,lt,le,ge,gt}
#   simd_lane_oracle_test.c   exhaustive over all 256x256 Int8 operand pairs
#
# The helpers are not written here.  They are extracted from a freshly
# generated .c, so the test always checks what the compiler emits today rather
# than a copy that can drift from it.
#
# Usage: run_simd_oracle_tests.sh [cc]
set -u
CC=${1:-gcc}
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0

GIBBON=${GIBBON_EXE:-$ROOT/dist-newstyle/build/x86_64-linux/ghc-9.10.1/gibbon-0.3/x/gibbon/build/gibbon/gibbon}
if [ ! -x "$GIBBON" ]; then
  echo "SKIP: no gibbon binary at $GIBBON (build it, or set GIBBON_EXE)"
  exit 0
fi

# Any program will do: the helpers live in the codegen prelude.
cat > "$TMP/tiny.hs" <<'EOF'
gibbon_main = 1
EOF

# Extract the helper set Gibbon emits for one --simd-isa into $2.
extract_helpers () { # isa  outfile
  local isa="$1" out="$2"
  ( cd "$TMP" && GIBBONDIR=$ROOT "$GIBBON" --packed --simd-isa="$isa" \
      --toC --cfile "tiny_$isa.c" tiny.hs ) >"$TMP/gen_$isa.log" 2>&1
  if [ ! -f "$TMP/tiny_$isa.c" ]; then
    echo "FAIL: could not generate C for --simd-isa=$isa"; tail -5 "$TMP/gen_$isa.log"
    return 1
  fi
  # The helper region runs from the first gib_vec_ definition to the closing
  # brace of the last one.  Everything in between -- the vector typedefs, the
  # comments -- comes with it, which is what the harnesses need.
  local first last
  first=$(grep -n '^static inline .*gib_vec_' "$TMP/tiny_$isa.c" | head -1 | cut -d: -f1)
  last=$(grep -n '^static inline .*gib_vec_' "$TMP/tiny_$isa.c" | tail -1 | cut -d: -f1)
  if [ -z "$first" ] || [ -z "$last" ]; then
    echo "FAIL: no gib_vec_ helpers in the C generated for --simd-isa=$isa"; return 1
  fi
  # Extend past the last helper's body.
  local endline
  endline=$(awk -v L="$last" 'NR>=L { print; n=gsub(/{/,"{"); m=gsub(/}/,"}"); d += n-m;
                                      if (started && d==0) { print NR > "/dev/stderr"; exit }
                                      if (n>0) started=1 }' \
              "$TMP/tiny_$isa.c" 2>&1 >/dev/null)
  [ -n "$endline" ] || endline=$last
  sed -n "${first},${endline}p" "$TMP/tiny_$isa.c" > "$TMP/body_$isa.h"
  {
    echo '#include <xmmintrin.h>'
    echo '#include <emmintrin.h>'
    echo '#ifdef __SSE4_1__'
    echo '#include <smmintrin.h>'
    echo '#endif'
    echo '#ifdef __AVX2__'
    echo '#include <immintrin.h>'
    echo '#endif'
    # The emitted int64 lane helpers call these RTS-side guarded operations.
    echo 'static inline int64_t gib_div_i64(int64_t a, int64_t b)'
    echo '{ return b == 0 ? 0 : (b == -1 && a == INT64_MIN ? a : a / b); }'
    echo 'static inline int64_t gib_mod_i64(int64_t a, int64_t b)'
    echo '{ return b == 0 ? 0 : (b == -1 ? 0 : a % b); }'
    cat "$TMP/body_$isa.h"
  } > "$out"
  local n; n=$(grep -c '^static inline .*gib_vec_' "$out")
  if [ "$n" -lt 20 ]; then
    echo "FAIL: extracted only $n SIMD helpers for --simd-isa=$isa"; return 1
  fi
  echo "extracted $n emitted SIMD helpers for --simd-isa=$isa"
}

run_one () { # test-source  label  extra-cflags...
  local src="$1" label="$2"; shift 2
  local bin="$TMP/$(basename "$src" .c)_$(echo "$label" | tr -c 'a-zA-Z0-9' _)"
  if ! $CC -O2 -std=gnu11 "$@" -o "$bin" "$ROOT/gibbon-rts/tests/$src" \
         -lm 2>"$TMP/cc.log"; then
    echo "  FAIL  $src [$label] did not compile"; sed -n '1,5p' "$TMP/cc.log"
    fail=$((fail+1)); return
  fi
  local out; out=$("$bin" 2>&1); local rc=$?
  if [ $rc -eq 0 ]; then
    echo "  PASS  $src [$label] :: $(tr '\n' ' ' <<<"$out" | tail -c 120)"
    pass=$((pass+1))
  else
    echo "  FAIL  $src [$label] rc=$rc :: $(tr '\n' ' ' <<<"$out" | tail -c 200)"
    fail=$((fail+1))
  fi
}

for spec in "-msse2:sse2:sse2" "-msse4.1:sse4.1:sse2" "-mavx2:avx2:avx2" "-march=native:native:avx2"; do
  cflags=${spec%%:*}; rest=${spec#*:}; label=${rest%%:*}; isa=${rest#*:}
  mkdir -p "$TMP/inc_$label"
  if extract_helpers "$isa" "$TMP/inc_$label/gib_simd_helpers.h"; then
    run_one simd_width_oracle_test.c "$label" "$cflags" -I "$TMP/inc_$label"
    run_one simd_lane_oracle_test.c  "$label" "$cflags" -I "$TMP/inc_$label"
  else
    fail=$((fail+2))
  fi
done

echo "simd oracle tests: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
