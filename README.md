# The tree-velocity project: Gibbon Language and Compiler

 * Travis: [![Build Status](https://travis-ci.org/iu-parfunc/gibbon.svg?branch=master)](https://travis-ci.org/iu-parfunc/gibbon)
 * Jenkins (somewhat unreliable):
   [![Build Status](http://parfunc-ci.sice.indiana.edu/buildStatus/icon?job=gibbon/master)](http://parfunc-ci.sice.indiana.edu/job/gibbon/job/master/)

Formerly the "tree-velocity" repo, this primarily stores the Gibbon
compiler, an implementation of a high-performance functional language.

This repository also contains a collection of sub-projects related to
benchmarking tree traversals and performing tree traversals on packed
representations.  Here is a guide to the subdirectories:

 * [gibbon-compiler](gibbon-compiler) - the prototype compiler for the Gibbon language of packed tree traversals.

 * [ASTBenchmarks](ASTBenchmarks) - benchmark of treewalks (compiler passes) on ASTs written with Gibbon.
   Also includes scripts to fetch input datasets.

 * `BintreeBench` - a submodule containing the tiniest binary tree microbenchmark, implemented several different languages and compilers.
   
 * [core-harvest](core-harvest) - tools to harvest realistic, large ASTs (mainly Racket) from the wild.
 
 * [DEVLOG.md](DEVLOG.md) - detailed documentation for those hacking on this repository.
