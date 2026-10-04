#!/usr/bin/env bash
# Fully-factored (SoA) indirections: every program in tests/factored_indirections
# shares a factored value instead of copying it.  Each must print its answer
# (derived by factored_indirections/model.py from the source) under every flag
# set below.  See Note [A factored indirection lives in the tag buffer].
#
# The `known` entries are compile failures that occur without any indirection
# (each has a reproducer that shares nothing); they are pinned so that fixing
# one shows up here.
#
#   M2  recursive writer that must traverse a field to reach the next, no RAN,
#       mutable cursors
#   M3  function that allocates a factored value in a local region, mutable
#       cursors
#
# Usage: factored_indirections.sh [gcc|clang]
set -u
: "${GIBBONDIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
export GIBBONDIR
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DIR="$HERE/factored_indirections"
GIBBON="${GIBBON_EXE:-$(find "$GIBBONDIR/dist-newstyle" -name gibbon -type f -path '*x/gibbon/build*' 2>/dev/null | head -1)}"
[ -x "$GIBBON" ] || { echo "FATAL: no gibbon executable (set GIBBON_EXE)"; exit 2; }
CC_FLAG="--cc=${1:-gcc}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0
chk () { if [ "$2" == "$3" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "  FAIL  $1: got [$2] want [$3]"; fi }

# Names and flag strings in parallel arrays: the flag strings contain spaces.
MODE_NAMES=(default noran noran_mut nogc nogc_noran mut_nonrec)
MODE_FLAGS=("" "--no-ran" "--no-ran --use-mutable-cursors" "--no-gc" "--no-gc --no-ran"
            "--use-mutable-cursors --opt-mutable-cursors-nonrec")

# $1 program, $2 mode -> "ok" or the known defect.
expect () {
  case "$1/$2" in
    PassThru/noran_mut|MultiBuf/noran_mut|BigTree/noran_mut) echo M2 ;;
    GcShare/noran_mut|GcSafe/noran_mut) echo M2 ;;
    GcShare/mut_nonrec|GcSafe/mut_nonrec) echo M3 ;;
    *) echo ok ;;
  esac
}

echo "== factored indirections: answers under every flag set =="
for prog in IdTree RightTree PassThru MultiBuf BigTree Spine GcShare GcSafe MixedLayout; do
  want_out=$(cat "$DIR/$prog.ans")
  for i in "${!MODE_NAMES[@]}"; do
    mode=${MODE_NAMES[$i]}; flags=${MODE_FLAGS[$i]}; want=$(expect "$prog" "$mode")
    if "$GIBBON" --packed $flags $CC_FLAG --to-exe --cfile="$TMP/$prog.c" \
         --exefile="$TMP/$prog.exe" "$DIR/$prog.hs" >"$TMP/$prog.build" 2>&1; then
      if [ "$want" != ok ]; then
        fail=$((fail+1)); echo "  FAIL  $prog/$mode: compiled, but $want was expected to stop it"
        continue
      fi
      chk "$prog/$mode" "$(timeout 120 "$TMP/$prog.exe" </dev/null 2>&1)" "$want_out"
    elif [ "$want" == ok ]; then
      fail=$((fail+1)); echo "  FAIL  $prog/$mode: compile failed"
      head -3 "$TMP/$prog.build" | sed 's/^/        /'
    else
      pass=$((pass+1))
    fi
  done
done

echo "== factored indirections: what is refused =="
# A shared tail consumed by two constructor alternatives: each writes one tag
# before it, so the tags coincide and no node fits.
sed 's/@N@/5/; s/"Linear"/"Factored"/' "$HERE/vw31/sharedTail.hs.in" > "$TMP/sharedTail.hs"
"$GIBBON" --packed --toC --cfile="$TMP/sharedTail.c" "$TMP/sharedTail.hs" >"$TMP/sharedTail.build" 2>&1
chk "factored shared tail refused" \
    "$(grep -c "fully factored (SoA), and its tag-buffer start is only 0 bytes" "$TMP/sharedTail.build")" "1"
"$GIBBON" --packed --gen-gc --toC --cfile="$TMP/gengc.c" "$DIR/IdTree.hs" >"$TMP/gengc.build" 2>&1
chk "factored indirection refused under --gen-gc" \
    "$(grep -c "cannot share a fully-factored (SoA) value under --gen-gc" "$TMP/gengc.build")" "1"

echo "factored_indirections: pass=$pass fail=$fail"
[ "$fail" -eq 0 ]
