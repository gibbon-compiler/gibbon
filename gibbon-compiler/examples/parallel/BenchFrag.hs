module BenchFrag where

import Coins
import BinTree
import KdTree
import FoldConstants

--------------------------------------------------------------------------------

bench_frag_seqbuildfib :: ()
bench_frag_seqbuildfib =
  let n = 18
      tr = (mkTreeFib_seq n)
      expected = (2 ^ n) * (fib_seq 20)
      n = iterate (sumTree_seq tr)
      _ = print_check (expected == n)
      _ = printint n
  in ()

bench_frag_parbuildfib :: ()
bench_frag_parbuildfib =
  let n = 18
      cutoff = 6
      tr = (mkTreeFib_par cutoff n)
      expected = (2 ^ n) * (fib_seq 20)
      n = iterate (sumTree_seq tr)
      _ = print_check (expected == n)
      _ = printint n
  in ()

loop_trav_buildfib :: Int -> Tree -> Int
loop_trav_buildfib iter tr =
    let n = sumTree_seq tr
    in if iter == 1
       then n
       else loop_trav_buildfib (iter-1) tr

bench_frag_seqbuildfib_loop :: ()
bench_frag_seqbuildfib_loop =
  let n = 18
      cutoff = 6
      tr = (mkTreeFib_seq n)
      expected = (2 ^ n) * (fib_seq 20)
      iters = sizeParam
      _ = printsym (quote "running ")
      _ = printint iters
      _ = printsym (quote " times.\n")
      m = iterate (loop_trav_buildfib iters tr)
      _ = print_check (expected == m)
      _ = printint m
  in ()

bench_frag_parbuildfib_loop :: ()
bench_frag_parbuildfib_loop =
  let n = 18
      cutoff = 6
      tr = (mkTreeFib_par cutoff n)
      expected = (2 ^ n) * (fib_seq 20)
      iters = sizeParam
      _ = printsym (quote "running ")
      _ = printint iters
      _ = printsym (quote " times.\n")
      m = iterate (loop_trav_buildfib iters tr)
      _ = print_check (expected == n)
      _ = printint m
  in ()


--------------------------------------------------------------------------------

bench_frag_seqbuildkdtree :: ()
bench_frag_seqbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        tr      = (mkKdTree_seq pts)
        n       = iterate (sumKdTree tr)
        _       = check_buildkdtree pts tr
        _       = printfloat n
    in ()

bench_frag_parbuildkdtree :: ()
bench_frag_parbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        cutoff  = 32000
        tr      = (mkKdTree_par cutoff pts)
        n       = iterate (sumKdTree tr)
        _       = check_buildkdtree pts tr
        _       = printfloat n
    in ()


loop_trav_buildkdtree :: Int -> KdTree -> Float
loop_trav_buildkdtree iter tr =
    let n = sumKdTree tr
    in if iter == 1
       then n
       else loop_trav_buildkdtree (iter-1) tr


bench_frag_seqbuildkdtree_loop :: ()
bench_frag_seqbuildkdtree_loop =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        tr      = (mkKdTree_seq pts)
        iters = sizeParam
        _ = printsym (quote "running ")
        _ = printint iters
        _ = printsym (quote " times.\n")
        n       = iterate (loop_trav_buildkdtree iters tr)
        _       = check_buildkdtree pts tr
        _       = printfloat n
    in ()


bench_frag_parbuildkdtree_loop :: ()
bench_frag_parbuildkdtree_loop =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        cutoff  = 32000
        tr      = (mkKdTree_par cutoff pts)
        iters = sizeParam
        _ = printsym (quote "running ")
        _ = printint iters
        _ = printsym (quote " times.\n")
        n       = iterate (loop_trav_buildkdtree iters tr)
        _       = check_buildkdtree pts tr
        _       = printfloat n
    in ()


--------------------------------------------------------------------------------

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
        amt = 999
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
        amt = 999
        tr = (payA_par 3 amt coins6)
        len = iterate (lenA tr)
        _ = printint len
    in ()

loop_trav_coins :: Int -> AList -> Int
loop_trav_coins iter tr =
    let n = lenA tr
    in if iter == 1
       then n
       else loop_trav_coins (iter-1) tr


bench_frag_seqcoins_loop :: ()
bench_frag_seqcoins_loop =
    let coins0 :: List (Int,Int)
        coins0 = alloc_ll
        coins1 = cons_ll (250,55) coins0
        coins2 = cons_ll (100,88) coins1
        coins3 = cons_ll (25,88) coins2
        coins4 = cons_ll (10,99) coins3
        coins5 = cons_ll (5,122) coins4
        coins6 = cons_ll (1,177) coins5
    -- in printCoins coins6
        amt = 999
        tr = (payA_seq amt coins6)
        iters = sizeParam
        _ = printsym (quote "running ")
        _ = printint iters
        _ = printsym (quote " times.\n")
        len = iterate (loop_trav_coins iters tr)
        _ = printint len
    in ()

bench_frag_parcoins_loop :: ()
bench_frag_parcoins_loop =
    let coins0 :: List (Int,Int)
        coins0 = alloc_ll
        coins1 = cons_ll (250,55) coins0
        coins2 = cons_ll (100,88) coins1
        coins3 = cons_ll (25,88) coins2
        coins4 = cons_ll (10,99) coins3
        coins5 = cons_ll (5,122) coins4
        coins6 = cons_ll (1,177) coins5
    -- in printCoins coins6
        amt = 999
        tr = (payA_par 3 amt coins6)
        iters = sizeParam
        _ = printsym (quote "running ")
        _ = printint iters
        _ = printsym (quote " times.\n")
        len = iterate (loop_trav_coins iters tr)
        _ = printint len
    in ()

--------------------------------------------------------------------------------

bench_frag_seqfoldconstants :: ()
bench_frag_seqfoldconstants =
    let exp = buildExp 26
        exp1 = (foldConstants2 exp)
        m = iterate (sumExp exp1)
        _ = printint m
    in ()

bench_frag_parfoldconstants :: ()
bench_frag_parfoldconstants =
    let exp = buildExp 26
        exp1 = (foldConstants2_par 0 exp)
        m = iterate (sumExp exp1)
        _ = printint m
    in ()

loop_trav_foldconstants :: Int -> Exp -> Int
loop_trav_foldconstants iter tr =
    let n = sumExp tr
    in if iter == 1
       then n
       else loop_trav_foldconstants (iter-1) tr

bench_frag_seqfoldconstants_loop :: ()
bench_frag_seqfoldconstants_loop =
    let exp = buildExp 26
        exp1 = (foldConstants2 exp)
        iters = sizeParam
        _ = printsym (quote "running ")
        _ = printint iters
        _ = printsym (quote " times.\n")
        m = iterate (loop_trav_foldconstants iters exp1)
        _ = printint m
    in ()

bench_frag_parfoldconstants_loop :: ()
bench_frag_parfoldconstants_loop =
    let exp = buildExp 26
        exp1 = (foldConstants2_par 0 exp)
        iters = sizeParam
        _ = printsym (quote "running ")
        _ = printint iters
        _ = printsym (quote " times.\n")
        m = iterate (loop_trav_foldconstants 26 exp1)
        _ = printint m
    in ()


--------------------------------------------------------------------------------

gibbon_main =
    if eqBenchProg "frag_seqbuildfib"
    then bench_frag_seqbuildfib
    else if eqBenchProg "frag_parbuildfib"
    then bench_frag_parbuildfib
    else if eqBenchProg "frag_seqbuildfib_loop"
    then bench_frag_seqbuildfib_loop
    else if eqBenchProg "frag_parbuildfib_loop"
    then bench_frag_parbuildfib_loop
    else if eqBenchProg "frag_seqbuildkdtree"
    then bench_frag_seqbuildkdtree
    else if eqBenchProg "frag_parbuildkdtree"
    then bench_frag_parbuildkdtree
    else if eqBenchProg "frag_seqbuildkdtree_loop"
    then bench_frag_seqbuildkdtree_loop
    else if eqBenchProg "frag_parbuildkdtree_loop"
    then bench_frag_parbuildkdtree_loop
    else if eqBenchProg "frag_seqcoins"
    then bench_frag_seqcoins
    else if eqBenchProg "frag_parcoins"
    then bench_frag_parcoins
    else if eqBenchProg "frag_seqcoins_loop"
    then bench_frag_seqcoins_loop
    else if eqBenchProg "frag_parcoins_loop"
    then bench_frag_parcoins_loop
    else if eqBenchProg "frag_seqfoldconstants"
    then bench_frag_seqfoldconstants
    else if eqBenchProg "frag_parfoldconstants"
    then bench_frag_parfoldconstants
    else if eqBenchProg "frag_seqfoldconstants_loop"
    then bench_frag_seqfoldconstants_loop
    else if eqBenchProg "frag_parfoldconstants_loop"
    then bench_frag_parfoldconstants_loop
    else ()
