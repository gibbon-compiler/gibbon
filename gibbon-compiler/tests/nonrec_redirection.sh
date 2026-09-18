#!/usr/bin/env bash
# --opt-mutable-cursors-nonrec on pure SoA readers that take the two paths on
# which a flag-off reader returns a region end other than the one it was
# passed: following a redirection, and jumping through a RAN pointer.
#
#   ReadAcrossChunks.hs  valOf     GIB_REDIRECTION_TAG branch  (RAN on and off)
#   RanReader.hs         rightVal  RAN branch (absran)         (RAN on)
#
# Each program's callers read a child just after writing it and then write the
# parent, and a final sumT re-reads the whole tree. For each fixture and mode,
# flag off and flag on:
#   * the generated C gets a counter on the fixture's branch, which must be
#     nonzero, so the test cannot pass without taking that path;
#   * the output must equal the fixture's .ans, a closed form of its source;
#   * with the flag the reader must return GibInt64 (the flag took effect),
#     and without it must not.
set -u
: "${GIBBONDIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
export GIBBONDIR
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GIBBON="${GIBBON_EXE:-$(find "$GIBBONDIR/dist-newstyle" -name gibbon -type f -path '*x/gibbon/build*' 2>/dev/null | head -1)}"
[ -x "$GIBBON" ] || { echo "FATAL: no gibbon executable (set GIBBON_EXE)"; exit 2; }
CC="${1:-gcc}"
RTS="$GIBBONDIR/gibbon-rts/build"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0
chk () { if [ "$2" == "$3" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "  FAIL  $1: got [$2] want [$3]"; fi }

MUT="--packed --use-mutable-cursors"
NORAN="--packed --no-ran --use-mutable-cursors"

# $1 = C file, $2 = output, $3 = function, $4 = marker regex; the counter is
# bumped on the line after each marker inside the function.
instrument () {
  awk -v fn="$3" -v marker="$4" '
    BEGIN { print "#include <stdio.h>\nstatic long branch_hits = 0;\n__attribute__((destructor)) static void report(void) { fprintf(stderr, \"HITS %ld\\n\", branch_hits); }" }
    $0 ~ ("^[A-Za-z][A-Za-z0-9_]* " fn "\\(") && !/;[ \t]*$/ { infn = 1 }
    /^}/ { infn = 0 }
    { print }
    infn && $0 ~ marker { print "branch_hits++;"; n++ }
    END { if (n == 0) exit 3 }
  ' "$1" > "$2"
}

# $1 = fixture stem, $2 = reader, $3 = marker regex, $4 = mode name, $5 = flags
run () {
  local stem=$1 fn=$2 marker=$3 mode=$4 flags=$5 flag extra tag base elided out hits
  local want; want=$(cat "$HERE/nonrec_redirection/$stem.ans")
  cp "$HERE/nonrec_redirection/$stem.hs" "$TMP/$stem.hs"
  for flag in off on; do
    extra=""; [ $flag = on ] && extra="--opt-mutable-cursors-nonrec"
    tag="$stem/$mode/$flag"
    base="$TMP/$stem.$mode.$flag"
    # --to-exe also (re)builds the RTS objects the instrumented build links against.
    if ! "$GIBBON" $flags $extra --cc="$CC" --to-exe --cfile="$base.c" --exefile="$base.exe" \
         "$TMP/$stem.hs" > "$base.build" 2>&1; then
      fail=$((fail+1)); echo "  FAIL  $tag: compile failed"; head -5 "$base.build" | sed 's/^/        /'; continue
    fi
    if grep -q "^GibInt64 $fn(" "$base.c"; then elided=yes; else elided=no; fi
    chk "$tag $fn returns GibInt64" "$elided" "$([ $flag = on ] && echo yes || echo no)"
    chk "$tag output" "$(timeout 60 "$base.exe" </dev/null 2>&1 | tail -1)" "$want"
    if ! instrument "$base.c" "$base.i.c" "$fn" "$marker"; then
      fail=$((fail+1)); echo "  FAIL  $tag: marker /$marker/ not found in $fn"; continue
    fi
    if ! "$CC" -std=gnu11 -O3 -flto -D_GIBBON_GENGC=0 -D_GIBBON_REGIONRESET=0 -D_GIBBON_SIMPLE_WRITE_BARRIER=0 \
         -D_GIBBON_EAGER_PROMOTION=1 -I"$RTS" -L"$RTS" -Wl,-rpath="$RTS" -o "$base.i.exe" "$base.i.c" \
         "$RTS/gibbon_rts.o" -lm -lgibbon_rts_ng > "$base.i.build" 2>&1; then
      fail=$((fail+1)); echo "  FAIL  $tag: instrumented build failed"; head -5 "$base.i.build" | sed 's/^/        /'; continue
    fi
    out=$(timeout 60 "$base.i.exe" </dev/null 2>"$base.i.err" | tail -1)
    hits=$(awk '/^HITS /{print $2}' "$base.i.err")
    chk "$tag instrumented output" "$out" "$want"
    if [ "${hits:-0}" -gt 0 ]; then pass=$((pass+1)); echo "  ok    $tag: $fn took the branch $hits times"
    else fail=$((fail+1)); echo "  FAIL  $tag: $fn never took the branch (hits=${hits:-none})"; fi
  done
}

run ReadAcrossChunks valOf    "case GIB_REDIRECTION_TAG:" mut   "$MUT"
run ReadAcrossChunks valOf    "case GIB_REDIRECTION_TAG:" noran "$NORAN"
run RanReader        rightVal "GibCursor end_absran_"     mut   "$MUT"

echo
echo "== nonrec redirection ($CC): $pass passed, $fail failed =="
[ $fail -eq 0 ]
