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
[Cabal](https://cabal.readthedocs.io/en/3.4/).

Follow the instructions below to have all dependencies. 

- Ubuntu 22.04:
(Parallelism support temporarily not available with ubuntu 22.04 as Cilk support is not avaiable with newer gcc)

```
 $ sudo apt-get update 
 $ sudo apt-get install software-properties-common 
 $ sudo apt-get install libgc-dev 
 $ sudo apt-get install libgmp-dev 
 $ sudo apt-get install build-essential 
 $ sudo apt-get install uthash-dev 
 $ sudo apt-get install vim wget curl
```

- Install Racket

```
 $ wget --no-check-certificate https://mirror.racket-lang.org/installers/7.5/racket-7.5-x86_64-linux.sh
 $ chmod +x racket-7.5-x86_64-linux.sh
 $ ./racket-7.5-x86_64-linux.sh
```

- Install haskell, cabal, stack, hls using ghcup 

```
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_GHC_VERSION=9.4.6 BOOTSTRAP_HASKELL_CABAL_VERSION=3.8.1.0 BOOTSTRAP_HASKELL_INSTALL_STACK=1 BOOTSTRAP_HASKELL_INSTALL_HLS=1 BOOTSTRAP_HASKELL_ADJUST_BASHRC=P sh
```

- Install rust 

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain=1.71.0
```

- Add paths for cabal, ghcup, rust to bashrc

- For Building on OSX:

You can install some of the dependencies using [Homebrew](https://brew.sh/):

    $ brew install libgc gmp gcc ghc@9

Others require a few extra steps:

1. Racket: Follow the instructions on it's [website](https://download.racket-lang.org/)

2. [uthash](https://github.com/troydhanson/uthash): Clone the [repository](https://github.com/troydhanson/uthash) and copy all the `.h` files in `src` to `/usr/local/include`


After you have both Cabal and all the dependencies installed, you can build
Gibbon from source:

    $ git clone https://github.com/iu-parfunc/gibbon
    $ cd gibbon && source set_env.sh
    $ cd gibbon-compiler && cabal v2-build . -w ghc-9.4.6

At this point you can run the Gibbon executable:

    $ cabal v2-exec -w ghc-9.4.6 gibbon -- -h

If you'd like to run the testsuite, you can do so with:

    $ cd $GIBBONDIR && ./run_all_tests.sh


## Building a Developement docker container for Gibbon 

To build the Dockerfile for dev purposes run the command below from the gibbon directory.

```
DOCKER_BUILDKIT=1 docker image build -t gibbon -f .devcontainer/Dockerfile .
```
Run the docker image using the following command. 

```
docker run -t -i gibbon
``` 

This image does not pre-populate the gibbon folder. Use git clone to clone gibbon into a folder. 
Use instructions from before to build gibbon.

## Building a Artifact version of Gibbon with the gibbon source code pre-populated 

To build a image with the gibbon source code already in the image run 

```
DOCKER_BUILDKIT=1 docker image build -t gibbon -f .artifact/Dockerfile .
```

Run the container with 

```
docker run -t -i gibbon
```

This has the gibbon source code avaiable in /gibbon

## Using Gibbon

A valid Gibbon program can be written using Haskell syntax or using Racket-like s-expression syntax.
Gibbon doesn't support every Haskell feature supported by GHC,
but informally, many simple Haskell-98 programs (sans monads) are valid Gibbon programs.
One thing to note is that the main point of entry for a Gibbon program is a
function named `gibbon_main`, as opposed to the usual `main`.
Here's a simple Gibbon program that builds a binary tree and sums up its leaves in parallel
using a parallel tuple (`par`):


```haskell
module Main where

data Tree = Leaf Int
          | Node Int Tree Tree

mkTree :: Int -> Tree
mkTree i =
  if i <= 0
  then Leaf 1
  else
      let x = (mkTree (i-1))
          y = (mkTree (i-1))
      in Node i x y

sumTree :: Tree -> Int
sumTree foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let tup = par (sumTree a) (sumTree b)
          x = fst tup
          y = snd tup
      in x + y

gibbon_main = sumTree (mkTree 10)
```

The Gibbon compiler is able to run in several modes, which are configured via command line flags.
Most important are the flags `--packed` which means "packed mode" (use serialized data structures),
`--run` which means "compile then run", and `--parallel` which means "enable parallel execution".
You can use these to run the above program as follows:

```
$ gibbon --run --packed --parallel Bintree.hs
```


This creates a file `Bintree.c` which contains the C-code,
and a `Bintree.exe` which is the executable for this program.
Running `./Bintree.exe` prints `1024`, the value of `sumTree (mkTree 10)`.
There are many other Gibbon features which can be learned by looking at the
programs under `./examples/parallel/`, and more flags
which can be printed with `gibbon --help`.
To view a complete set of primitives supported by Gibbon, you can look at the `Gibbon.Prim`
module located at `gibbon/gibbon-stdlib/Gibbon/Prim.hs`.


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
