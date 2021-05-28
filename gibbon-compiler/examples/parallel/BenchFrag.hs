module BenchFrag where

import Coins
import BinTree
import KdTree
import FoldConstants

bench_frag_seqbuildfib :: ()
bench_frag_seqbuildfib =
  let n = sizeParam
      tr = (mkTreeFib_seq n)
      expected = (2 ^ n) * (fib_seq 20)
      n = iterate (sumTree_seq tr)
      _ = print_check (expected == n)
      _ = printint n
  in ()

bench_frag_parbuildfib :: ()
bench_frag_parbuildfib =
  let n = sizeParam
      cutoff = 6
      tr = (mkTreeFib_par cutoff n)
      expected = (2 ^ n) * (fib_seq 20)
      n = iterate (sumTree_seq tr)
      _ = print_check (expected == n)
      _ = printint n
  in ()

bench_frag_seqbuildkdtree :: ()
bench_frag_seqbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n       = sizeParam
        radius  = intToFloat n
        tr      = (mkKdTree_seq pts)
        n       = iterate (sumKdTree tr)
        _       = check_buildkdtree pts tr
        _       = printfloat n
    in ()

bench_frag_parbuildkdtree :: ()
bench_frag_parbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n       = sizeParam
        radius  = intToFloat n
        cutoff  = 32000
        tr      = (mkKdTree_par cutoff pts)
        n       = iterate (sumKdTree tr)
        _       = check_buildkdtree pts tr
        _       = printfloat n
    in ()

bench_frag_seqcoins :: ()
bench_frag_seqcoins =
    let coins0 :: List (Int,Int)
        coins0 = alloc_ll
        coins1 = cons_ll (250,55) coins0
        coins2 = cons_ll (100,88) coins1
        coins3 = cons_ll (25,88) coins2
        coins4 = cons_ll (10,99) coins3
        coins5 = cons_ll (5,122) coins4
        coins6 = cons_ll (1,177) coins5
        amt = sizeParam
        tr = (payA_seq amt coins6)
        len = iterate (lenA tr)
        _ = printint len
    in ()

bench_frag_parcoins :: ()
bench_frag_parcoins =
    let coins0 :: List (Int,Int)
        coins0 = alloc_ll
        coins1 = cons_ll (250,55) coins0
        coins2 = cons_ll (100,88) coins1
        coins3 = cons_ll (25,88) coins2
        coins4 = cons_ll (10,99) coins3
        coins5 = cons_ll (5,122) coins4
        coins6 = cons_ll (1,177) coins5
    -- in printCoins coins6
        amt = sizeParam
        tr = (payA_par 3 amt coins6)
        len = iterate (lenA tr)
        _ = printint len
    in ()

bench_frag_seqfoldconstants :: ()
bench_frag_seqfoldconstants =
    let exp = buildExp sizeParam
        exp1 = (foldConstants2 exp)
        m = iterate (sumExp exp1)
        _ = printint m
    in ()

bench_frag_parfoldconstants :: ()
bench_frag_parfoldconstants =
    let exp = buildExp sizeParam
        exp1 = (foldConstants2_par 0 exp)
        m = iterate (sumExp exp1)
        _ = printint m
    in ()

gibbon_main =
    if eqBenchProg "frag_seqbuildfib"
    then bench_frag_seqbuildfib
    else if eqBenchProg "frag_parbuildfib"
    then bench_frag_parbuildfib
    else if eqBenchProg "frag_seqbuildkdtree"
    then bench_frag_seqbuildkdtree
    else if eqBenchProg "frag_parbuildkdtree"
    then bench_frag_parbuildkdtree
    else if eqBenchProg "frag_seqcoins"
    then bench_frag_seqcoins
    else if eqBenchProg "frag_parcoins"
    then bench_frag_parcoins
    else if eqBenchProg "frag_seqfoldconstants"
    then bench_frag_seqfoldconstants
    else if eqBenchProg "frag_parfoldconstants"
    then bench_frag_parfoldconstants
    else ()
