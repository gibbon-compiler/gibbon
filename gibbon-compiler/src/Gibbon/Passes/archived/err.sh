#!/usr/bin/env bash

basefile=$1

# Having some kind of weird race condition when running with make -j

# if [ -e "$basefile.out" ]; then
#    mv $basefile.out $basefile.err
#    echo Errored, moving output to file: $basefile.err
#else 
    touch $basefile.err
    echo Error while processing $basefile
#fi
exit 1
