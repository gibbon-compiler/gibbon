#!/bin/bash

mkdir runlogs
mkdir results
NOW=$(date +"%Y-%m-%d-%H-%M-%S")



echo "benchmarking updateTree varient........... "
_OutFile="log_updateTree""$NOW"

for _size in   100 1000 10000 100000 1000000 10000000 100000000
do
./bin/unpacked $1 $_size updatetree >> ./runlogs/$_OutFile
./bin/bumpalloc $1 $_size  updatetree >> ./runlogs/$_OutFile
./bin/packed $1 $_size  updatetree >>     ./runlogs/$_OutFile
./bin/packed_enhanced $1 $_size  updatetree >> ./runlogs/$_OutFile
done
grep '^res:\['  ./runlogs/$_OutFile |sed -e 's/res:\[//g' -e 's/\]//g'  >>./results/"data_benchmark_updateTree_$2_""$NOW"".csv"
echo "done benchmarking updateTree varient........... "

echo "benchmarking intOut varient.............. "
_OutFile="log_intOut""$NOW"

for _size in     100 1000 10000 100000 1000000 10000000 100000000
do
./bin/unpacked $1 $_size intout >>  ./runlogs/$_OutFile
./bin/bumpalloc $1 $_size intout >> ./runlogs/$_OutFile
./bin/packed $1 $_size intout >>     ./runlogs/$_OutFile
./bin/packed_enhanced $1 $_size intout >> ./runlogs/$_OutFile
done


grep '^res:\['  ./runlogs/$_OutFile |sed -e 's/res:\[//g' -e 's/\]//g'  >>./results/"data_benchmark_intOut_$2_""$NOW"".csv"
echo "done benchmarking intOut varient.............. "

echo "benchmarking treeOut varient.............. "
_OutFile="log_treeOut""$NOW"
for _size in    100 1000 10000 100000 1000000 10000000 100000000
do
./bin/unpacked $1 $_size treeout >> ./runlogs/$_OutFile
./bin/bumpalloc $1 $_size treeout >> ./runlogs/$_OutFile
./bin/packed $1 $_size treeout >>     ./runlogs/$_OutFile
./bin/packed_enhanced $1 $_size  treeout >> ./runlogs/$_OutFile
done
grep '^res:\['  ./runlogs/$_OutFile |sed -e 's/res:\[//g' -e 's/\]//g'  >>./results/"data_benchmark_treeOut_$2_""$NOW"".csv"
echo "done benchmarking treeOut varient.............. "
