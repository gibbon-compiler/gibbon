# The Gibbon Language and Compiler

[![Build Status](https://travis-ci.org/iu-parfunc/gibbon.svg?branch=master)](https://travis-ci.org/iu-parfunc/gibbon)

*Gibbon* is an experimental compiler that transforms high-level functional programs
to operate on _serialized data._

Typically, programs that process tree-like data represent trees using pointer-based
data structures in memory (one heap object per-leaf and per-node) because such a 
layout is convenient to manipulate in a high-level programming language. 
This is also generally distinct from the representation of the data in 
serialized form on disk,
which means that a program must perform some sort or marshaling when working with serialized data.
Gibbon _unifies_ the in-memory and serialized formats, transforming recursive
functions to operate _directly_ on serialized data.

Additionally, while the pointer-based structure is efficient
for random access and shape-changing modifications, it can be inefficient 
for traversals that process most or all of a tree in bulk. 
The Gibbon project aims to explore optimizations of recursive tree transforms 
by changing how trees are stored in memory. 

Currently, the Gibbon compiler has multiple front-ends: an s-expression synax
similar to Typed Racket, and a small subset of Haskell.

## Building Gibbon

Gibbon is implemented in Haskell, and is set up to be built with
[Stack](https://docs.haskellstack.org/en/stable/README/). After you
install Stack, proceed to installing Gibbon's dependencies.

On Ubuntu, you can install them with:

    $ sudo apt-get install libgc-dev libgmp-dev gcc-7


On OSX, install them using [Homebrew](https://brew.sh/):

    $ brew install libgc gmp


After you have both Stack and all the dependencies installed, you can build
Gibbon from source:

    $ git clone https://github.com/iu-parfunc/gibbon && cd gibbon/gibbon-compiler
    $ stack setup && stack build

At this point you can run the Gibbon executable:

    $ stack exec -- gibbon -h

## About this repository 

This primarily stores the Gibbon
compiler, an implementation of a high-performance functional language.

This repository also contains a collection of sub-projects related to
benchmarking tree traversals and performing tree traversals on packed
representations.  Here is a guide to the subdirectories:

 * [gibbon-compiler](gibbon-compiler) - the prototype compiler for the Gibbon language of packed tree traversals.

 * [gibbon](gibbon) - a Racket #lang for Gibbon.

 * [ASTBenchmarks](ASTBenchmarks) - benchmark of treewalks (compiler passes) on ASTs written with Gibbon.
   Also includes scripts to fetch input datasets.

 * `BintreeBench` - a submodule containing the tiniest binary tree microbenchmark, implemented several different languages and compilers.
   
 * [core-harvest](core-harvest) - tools to harvest realistic, large ASTs (mainly Racket) from the wild.
 
 * [DEVLOG.md](DEVLOG.md) - detailed documentation for those hacking on this repository.
