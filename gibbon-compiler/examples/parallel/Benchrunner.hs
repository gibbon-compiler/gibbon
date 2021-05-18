{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude   #-}

module Benchrunner where

import Fib
import BinTree
import KdTree
import Bhut
import Coins
import Countnodes
{- import Ray -}
import FoldConstants
import RacketGrammar

import Gibbon.Prelude
import Gibbon.Vector

--------------------------------------------------------------------------------

bench_seqfib :: ()
bench_seqfib =
    let n = sizeParam
        m = iterate (fib_seq n)
        _ = printint m
        _ = printsym (quote "\n")
    in ()

bench_parfib :: ()
bench_parfib =
    let n = sizeParam
        cutoff = 30
        m = iterate (fib_par cutoff n)
        _ = printint m
        _ = printsym (quote "\n")
    in ()

bench_seqbuildfib :: ()
bench_seqbuildfib =
  let n = sizeParam
      x = iterate (mkTreeFib_seq n)
  in check_buildfib n x

bench_parbuildfib :: ()
bench_parbuildfib =
  let n = sizeParam
      cutoff = 6
      x = iterate (mkTreeFib_par cutoff n)
  in check_buildfib n x


bench_seqbuildtree :: ()
bench_seqbuildtree =
    let n = sizeParam
        tr = iterate (mkTree_seq n)
    in check_buildtree n tr

bench_parbuildtree :: ()
bench_parbuildtree =
    let n = sizeParam
        cutoff = 19
        tr = iterate (mkTree_par cutoff n)
    in check_buildtree n tr

bench_seqadd1tree :: ()
bench_seqadd1tree =
    let n = sizeParam
        tr = mkTree_seq n
        tr1 = iterate (add1Tree_seq tr)
    in check_add1tree n tr1

bench_paradd1tree :: ()
bench_paradd1tree =
    let n = sizeParam
        tr = mkTree_seq n
        cutoff = 19
        tr1 = iterate (add1Tree_par cutoff tr)
    in check_add1tree n tr1

bench_seqsumtree :: ()
bench_seqsumtree =
    let n = sizeParam
        tr = mkTree_seq n
        actual = iterate (sumTree_seq tr)
    in check_sumtree n actual

bench_parsumtree :: ()
bench_parsumtree =
    let n = sizeParam
        tr = mkTree_seq n
        cutoff = 19
        actual = iterate (sumTree_par cutoff tr)
    in check_sumtree n actual

bench_seqbuildkdtree :: ()
bench_seqbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (mkKdTree_seq pts)
    in check_buildkdtree pts tr

bench_parbuildkdtree :: ()
bench_parbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n       = sizeParam
        radius  = intToFloat n
        -- cutoff  = 524288
        cutoff  = 32000
        tr      = iterate (mkKdTree_par cutoff pts)
    in check_buildkdtree pts tr

bench_seqcountcorr :: ()
bench_seqcountcorr =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n   = sizeParam
        radius  = 100.0
        tr      = mkKdTree_seq pts
        pts' = slice 0 n pts
        counts = iterate (allCountCorr_seq radius tr pts')
        query = nth pts' 4
        count = nth counts 4
    in ()

bench_parcountcorr :: ()
bench_parcountcorr =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n   = sizeParam
        radius  = 100.0
        tr      = mkKdTree_seq pts
        cutoff  = 8000
        pts' = slice 0 n pts
        counts = iterate (allCountCorr_par cutoff radius tr pts')
        query = nth pts' 4
        count = nth counts 4
    in ()

bench_seqnearest :: ()
bench_seqnearest =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        tr     = mkKdTree_seq pts
        nns = iterate (allNearest_seq tr pts)
    in check_nearest pts nns

bench_parnearest :: ()
bench_parnearest =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        tr     = mkKdTree_seq pts
        nns = iterate (allNearest_par tr pts)
     in check_nearest pts nns

bench_seqbuildquadtree :: ()
bench_seqbuildquadtree =
  let pts :: Vector (Float, Float)
      pts = readArrayFile Nothing
      particles  = map (\(pt :: (Float, Float)) ->
                            let (x,y) = pt
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let (x,y) = pt
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (fst pt) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (snd pt) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (fst pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (snd pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      tr = iterate (buildQtree_seq box mpts)
  in check_buildquadtree mpts tr

bench_parbuildquadtree :: ()
bench_parbuildquadtree =
  let pts :: Vector (Float, Float)
      pts = readArrayFile Nothing
      particles  = map (\(pt :: (Float, Float)) ->
                            let (x,y) = pt
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let (x,y) = pt
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (fst pt) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (snd pt) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (fst pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (snd pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      cutoff = 524288
      tr = iterate (buildQtree_par cutoff box mpts)
  in check_buildquadtree mpts tr

bench_seqbhut :: ()
bench_seqbhut =
  let pts :: Vector (Float, Float)
      pts = readArrayFile Nothing

      particles  = map (\(pt :: (Float, Float)) ->
                            let (x,y) = pt
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let (x,y) = pt
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (fst pt) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (snd pt) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (fst pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (snd pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      bht = buildQtree_seq box mpts
      particles1 = oneStep_seq bht mpts particles
  in ()

bench_parbhut :: ()
bench_parbhut =
  let pts :: Vector (Float, Float)
      pts = readArrayFile Nothing

      particles  = map (\(pt :: (Float, Float)) ->
                            let (x,y) = pt
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let (x,y) = pt
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (fst pt) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (snd pt) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (fst pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (snd pt) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      bht = buildQtree_seq box mpts
      cutoff = 524288
      particles1 = oneStep_par cutoff bht mpts particles
  in ()

bench_seqcoins :: ()
bench_seqcoins =
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
        tr = iterate (payA_seq amt coins6)
    in ()

bench_parcoins :: ()
bench_parcoins =
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
        tr = iterate (payA_par 3 amt coins6)
    in ()

bench_seqcountnodes :: ()
bench_seqcountnodes =
  let e = readPackedFile @Toplvl Nothing
      -- to ensure that mmap'd stuff is in memory.
      _ = countNodesSeq e
      n = iterate (countNodesSeq e)
      _ = printint n
      _ = printsym (quote "\n")
  in ()

bench_parcountnodes :: ()
bench_parcountnodes =
  let e = readPackedFile @Toplvl Nothing
      -- to ensure that mmap'd stuff is in memory.
      _ = countNodesSeq e
      n = iterate (countNodesPar e)
      _ = printint n
      _ = printsym (quote "\n")
  in ()

bench_seqfoldconstants :: ()
bench_seqfoldconstants =
    let exp = buildExp sizeParam
        exp1 = iterate (foldConstants2 exp)
        m = sumExp exp1
        _ = printint m
    in ()

bench_parfoldconstants :: ()
bench_parfoldconstants =
    let exp = buildExp sizeParam
        exp1 = iterate (foldConstants2_par 0 exp)
        m = sumExp exp1
        _ = printint m
    in ()

gibbon_main =
    if eqBenchProg "seqfib"
    then bench_seqfib
    else if eqBenchProg "parfib"
    then bench_parfib
    else if eqBenchProg "seqbuildfib"
    then bench_seqbuildfib
    else if eqBenchProg "parbuildfib"
    then bench_parbuildfib
    else if eqBenchProg "seqbuildtree"
    then bench_seqbuildtree
    else if eqBenchProg "parbuildtree"
    then bench_parbuildtree
    else if eqBenchProg "seqadd1tree"
    then bench_seqadd1tree
    else if eqBenchProg "paradd1tree"
    then bench_paradd1tree
    else if eqBenchProg "seqsumtree"
    then bench_seqsumtree
    else if eqBenchProg "parsumtree"
    then bench_parsumtree
    else if eqBenchProg "seqbuildkdtree"
    then bench_seqbuildkdtree
    else if eqBenchProg "parbuildkdtree"
    then bench_parbuildkdtree
    else if eqBenchProg "seqcountcorr"
    then bench_seqcountcorr
    else if eqBenchProg "parcountcorr"
    then bench_parcountcorr
    else if eqBenchProg "seqnearest"
    then bench_seqnearest
    else if eqBenchProg "parnearest"
    then bench_parnearest
    else if eqBenchProg "seqbuildquadtree"
    then bench_seqbuildquadtree
    else if eqBenchProg "parbuildquadtree"
    then bench_parbuildquadtree
    else if eqBenchProg "seqbhut"
    then bench_seqbhut
    else if eqBenchProg "parbhut"
    then bench_parbhut
    else if eqBenchProg "seqcoins"
    then bench_seqcoins
    else if eqBenchProg "parcoins"
    then bench_parcoins
    else if eqBenchProg "seqcountnodes"
    then bench_seqcountnodes
    else if eqBenchProg "parcountnodes"
    then bench_parcountnodes
{-
    else if eqBenchProg "seqmkbvh"
    then bench_seqmkbvh
    else if eqBenchProg "parmkbvh"
    then bench_parmkbvh
    else if eqBenchProg "seqray"
    then bench_seqray
    else if eqBenchProg "parray"
    then bench_parray
-}
    else if eqBenchProg "seqfoldconstants"
    then bench_seqfoldconstants
    else if eqBenchProg "parfoldconstants"
    then bench_parfoldconstants
    else printsym (quote "benchrunner: select benchmark to run with --bench-prog\n")
