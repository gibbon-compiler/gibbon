#!/usr/bin/env bash
# Programs that once compiled wrongly or not at all, each checked against its
# answer file under every flag set listed for it below.
#
# Usage: fi_fixes.sh [gcc|clang]
set -u
: "${GIBBONDIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
export GIBBONDIR
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DIR="$HERE/fi_fixes"
GIBBON="${GIBBON_EXE:-$(find "$GIBBONDIR/dist-newstyle" -name gibbon -type f -path '*x/gibbon/build*' 2>/dev/null | head -1)}"
[ -x "$GIBBON" ] || { echo "FATAL: no gibbon executable (set GIBBON_EXE)"; exit 2; }
CC_FLAG="--cc=${1:-gcc}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0

MUT="--use-mutable-cursors"
NONREC="--use-mutable-cursors --opt-mutable-cursors-nonrec"
# program|flag set, one per line; every flag set the program is checked under.
CASES=$(cat <<EOC
LinearFieldRead|
LinearFieldRead|--no-ran
LinearFieldRead|$MUT
LinearFieldRead|--no-ran $MUT
LinearFieldRead|$NONREC
LinearFieldRead|--no-ran $NONREC
EOC
)

while IFS='|' read -r prog flags; do
  [ -n "$prog" ] || continue
  want=$(cat "$DIR/$prog.ans")
  if "$GIBBON" --packed $flags $CC_FLAG --to-exe --cfile="$TMP/$prog.c" \
       --exefile="$TMP/$prog.exe" "$DIR/$prog.hs" >"$TMP/$prog.build" 2>&1; then
    got=$(timeout 120 "$TMP/$prog.exe" </dev/null 2>&1)
    if [ "$got" == "$want" ]; then pass=$((pass+1))
    else fail=$((fail+1)); echo "  FAIL  $prog [$flags]: got [$got] want [$want]"; fi
  else
    fail=$((fail+1)); echo "  FAIL  $prog [$flags]: compile failed"
    head -3 "$TMP/$prog.build" | sed 's/^/        /'
  fi
done <<< "$CASES"

echo "fi_fixes: pass=$pass fail=$fail"
[ "$fail" -eq 0 ]
