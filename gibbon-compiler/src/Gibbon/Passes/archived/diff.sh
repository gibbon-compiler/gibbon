#!/usr/bin/env bash

set +e

function checkfile() {
    if ! [ -e "$1" ]; then
        echo "File does not exist, cannot diff!: " $1
        exit 1
    fi
}

checkfile $1
checkfile $2

A=`mktemp`
B=`mktemp`

# TEMP: This ignores NEWLINES [2017.01.11].  May want to revert that eventually:
grep -v SELFTIMED $1 | grep -v BATCHTIME | tr '\n' ' ' > $A
grep -v SELFTIMED $2 | grep -v BATCHTIME | tr '\n' ' ' > $B
# did not work:
# sed -e ':a' -e 'N' -e '$!ba' -e 's/\n/ /g' 

# Policy: ignore whitespace on diff:
diff -w $A $B
code=$?

rm $A $B

if [ "$code" == "0" ]; then
    #    echo "  -> Success.";
    exit $code;
else
    echo "ERROR: Answers differed!: diff $1  $2";
    exit $code;
fi
