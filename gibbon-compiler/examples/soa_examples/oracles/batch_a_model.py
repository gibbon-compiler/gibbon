#!/usr/bin/env python3
"""Independent Python oracle for Batch A: List.hs, LinearListReduction.hs,
reduceNestedList.hs, TernaryTree.hs, and MonoTree.hs. Every program
modeled here uses Int64 consistently for its semantic integer data.

Nothing here reads Gibbon output.  Each function recomputes the program's
result directly from its OWN source definition (closed-form where the
recursion telescopes into simple arithmetic), at the exact size baked into
that program's `gibbon_main`.

`wrap64` (two's-complement Int64 wraparound) is still applied at the
closed-form summation boundary in every model that has one, keeping this
model's operation-by-operation Int64 wrapping discipline as the
reference value regardless of whether a given program's true total turns
out to need it. For every program modeled here, the true (unwrapped)
bignum total is comfortably inside Int64's +-9.223e18 range (List's
~5.0e15, LinearListReduction's ~5.0e13, reduceNestedList's ~5.0e11,
MonoTree's ~2.3e9), so `wrap64` is an identity on all of them at the
committed sizes.

Usage:  batch_a_model.py <program-stem>
"""
import sys
import ctypes


def wrap64(x: int) -> int:
    return ctypes.c_int64(x).value


def list_sum(n: int):
    # List.hs's Cons payload, mkList's build counter, add1's arithmetic,
    # and sumList/sumListAcc's accumulators are all natively Int64.
    # mkList n builds values n,n-1,...,1; add1 makes them
    # n+1,...,2; sumList/sumListAcc both total sum_{k=2}^{n+1} k. At the
    # committed n=100,000,000 the true sum is 5,000,000,150,000,000, well
    # inside Int64's range -- `wrap64` is an identity here, applied only
    # for consistency with the operation-by-operation-wrap discipline.
    total = wrap64((n + 1) * (n + 2) // 2 - 1)
    return "'#(%d %d %d)" % (total, total, n)


def linear_list_reduction(n: int):
    # LinearListReduction.hs: mkList n builds n+1 nodes whose ten fields all
    # hold the node's value, n down to 0. Each pass is derived here from that
    # shape rather than from the Haskell:
    #   reduce      sums field a                        -> n(n+1)/2
    #   maxField    largest value in field g            -> n
    #   countHeavy  nodes whose field e exceeds 32      -> n - 32
    #   bumpFirst   a := a + 7, summed over field a     -> n(n+1)/2 + 7(n+1)
    #   shiftTriple c := c + 3, summed over field c     -> n(n+1)/2 + 3(n+1)
    #   touchMost   a := a + 1, summed over field a     -> n(n+1)/2 + (n+1)
    # Every total fits inside Int64 at the committed n, so wrap64 is an
    # identity; it is applied anyway, as everywhere else in this model.
    nodes = n + 1
    total = wrap64(n * (n + 1) // 2)
    return "'#(%d %d %d %d %d %d)" % (
        total, n, n - 32,
        wrap64(total + 7 * nodes),
        wrap64(total + 3 * nodes),
        wrap64(total + nodes))


def linear_list_reduction_sum(n: int):
    # LinearListReduction.hs: mkList n builds nodes valued n,n-1,...,0;
    # reduce sums field `a` (== the node's value) over all n+1 nodes as a
    # genuine Int64 accumulator. True bignum total
    # n*(n+1)/2 = 50,000,005,000,000 at the committed n=10,000,000 fits
    # comfortably inside Int64 -- `wrap64` is an identity here.
    return str(wrap64(n * (n + 1) // 2))


def reduce_nested_list_sum(n: int):
    # reduceNestedList.hs: mkList n builds outer nodes valued n,n-1,...,1;
    # reduce sums only the outer field (the fixed-length-3000 inner ListA
    # is unused), as a genuine Int64 accumulator. True bignum total
    # n*(n+1)/2 = 500,000,500,000 at the
    # committed n=1,000,000 fits comfortably inside Int64 -- `wrap64` is an
    # identity here.
    return str(wrap64(n * (n + 1) // 2))


def ternary_tree_sum(d: int):
    # TernaryTree.hs: mkTree d builds a ternary tree of depth d; every leaf
    # holds 0 and every internal node holds 1 before add1Tree, so after
    # add1Tree every leaf holds 1 and every internal node holds 2. Total is
    # tiny (28,697,813 at d=15) -- always fit Int32 and trivially fits
    # Int64; no wrap needed at either width.
    internal = (3 ** d - 1) // 2
    leaves = 3 ** d
    return str(internal * 2 + leaves * 1)


def mono_tree_sum(d: int):
    # MonoTree.hs: mkTree d 0 builds a complete binary tree of depth d;
    # every leaf's accumulated value is 1+2+...+d = d(d+1)/2 regardless of
    # path (both children of a node always receive the same d+acc), so
    # after add1Tree every one of the 2^d leaves holds d(d+1)/2 + 1.
    # sumTree/sumTreeAcc are Int64: the true bignum total at the committed
    # d=23 is 2,323,644,416, comfortably inside Int64's range (though past
    # Int32's), so `wrap64` here is an identity, applied only for
    # consistency with the operation-by-operation-wrap discipline.
    leaf_val = d * (d + 1) // 2 + 1
    total = wrap64((2 ** d) * leaf_val)
    return "'#(%d %d)" % (total, total)


MODELS = {
    "List": lambda: list_sum(100000000),
    "LinearListReduction": lambda: linear_list_reduction(10000000),
    "reduceNestedList": lambda: reduce_nested_list_sum(1000000),
    "TernaryTree": lambda: ternary_tree_sum(15),
    "MonoTree": lambda: mono_tree_sum(23),
}

if __name__ == "__main__":
    stem = sys.argv[1]
    print(MODELS[stem]())
