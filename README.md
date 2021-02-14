# The Gibbon Compiler

![test-gibbon](https://github.com/iu-parfunc/gibbon/workflows/test-gibbon/badge.svg?branch=master)

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

- Ubuntu:

```
 $ sudo apt-get install libgc-dev libgmp-dev gcc-7 uthash-dev
 $ sudo add-apt-repository ppa:plt/racket && sudo apt update && sudo apt install racket
```


- OSX:

You can install some of the dependencies using [Homebrew](https://brew.sh/):

    $ brew install libgc gmp

Others require a few extra steps:

1. Racket: Follow the instructions on it's [website](https://download.racket-lang.org/)

2. [uthash](https://github.com/troydhanson/uthash): Clone the [repository](https://github.com/troydhanson/uthash) and copy all the `.h` files in `src` to `/usr/local/include`


After you have both Stack and all the dependencies installed, you can build
Gibbon from source:

    $ git clone https://github.com/iu-parfunc/gibbon
    $ cd gibbon && source set_env.sh
    $ cd gibbon-compiler && stack setup && stack build

At this point you can run the Gibbon executable:

    $ stack exec -- gibbon -h

If you'd like to run the testsuite, you can do so with:

    $ cd $GIBBONDIR && ./run_all_tests.sh

## Using Gibbon

Gibbon can be run in multiple modes. The `-r` flag indicates that you want to
compile and run a program:

    $ gibbon -r ./demo/Add1.hs

If the extension is `*.hs`, it is assumed to be a Haskell source file, and if it
is `*.gib` it is a Racket source file starting with `#lang gibbon`. 

Just the `-r` flag by itself will apply the high-level specialization optimizations
but will not use packed data. The `-p` flag instructs Gibbon to use
a packed representation whenever possible. These can be combined:

    $ gibbon -rp ./demo/PolyTree.hs

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
