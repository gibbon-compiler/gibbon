#!/bin/bash
# --interp1 must print what the compiled program prints.
#
# The compiled --pointer binary is the oracle: it is what every recorded result
# in this project was produced with.  The programs cover all four integer
# widths, floats, bools, printPacked and the special symbols, because the
# interpreter reached each of those through a different arm.
#
# Usage: run_interp1_tests.sh [path-to-gibbon]
set -u

GIBBON=${1:-}
if [ -z "$GIBBON" ]; then
  GIBBON=$(command -v gibbon)
fi
if [ ! -x "$GIBBON" ]; then
  echo "run_interp1_tests.sh: no gibbon executable (pass one as \$1)" >&2
  exit 2
fi

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
export GIBBONDIR=$ROOT
SRCDIR=$HERE/interp1
WD=$(mktemp -d)
trap 'rm -rf "$WD"' EXIT

pass=0; fail=0

for src in "$SRCDIR"/*.hs; do
  b=$(basename "$src" .hs)
  cp "$src" "$WD/$b.hs"
  ( cd "$WD" && ulimit -v 24000000
    "$GIBBON" --pointer --to-exe -o "$b.exe" "$b.hs" ) > "$WD/$b.build.log" 2>&1
  if [ ! -x "$WD/$b.exe" ]; then
    fail=$((fail+1)); echo "  FAIL  $b (the --pointer oracle does not build)"
    sed -n '1,6p' "$WD/$b.build.log" | sed 's/^/          /'
    continue
  fi
  ptr=$( cd "$WD" && ulimit -v 24000000; timeout 300 "./$b.exe" 2>/dev/null )
  itp=$( cd "$WD" && ulimit -v 24000000; timeout 300 "$GIBBON" --interp1 "$b.hs" 2>/dev/null )
  if [ "$ptr" = "$itp" ]; then
    pass=$((pass+1)); echo "  PASS  $b"
  else
    fail=$((fail+1))
    echo "  FAIL  $b (output differs)"
    diff <(printf '%s\n' "$ptr") <(printf '%s\n' "$itp") | sed 's/^/          /'
  fi
done

echo "interp1-vs-pointer: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
