{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude   #-}

module Benchrunner where

-- import Fib
-- import BinTree
import KdTree
import Bhut
-- import Coins
-- import Countnodes
{- import Ray -}
import FoldConstants
-- import RacketGrammar

import Gibbon.Prelude
import Gibbon.Vector

--------------------------------------------------------------------------------

bench_seqbuildkdtree :: ()
bench_seqbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (mkKdTree_seq pts)
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
    in check_countcorr pts' query count radius

bench_seqnearest :: ()
bench_seqnearest =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile Nothing
        tr     = mkKdTree_seq pts
        nns = iterate (allNearest_seq tr pts)
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
      _ = check_buildquadtree mpts bht
      particles1 = oneStep_seq bht mpts particles
  in ()

bench_seqfoldconstants :: ()
bench_seqfoldconstants =
    let exp = buildExp sizeParam
        exp1 = iterate (foldConstants2 exp)
        m = sumExp exp1
        _ = printint m
    in ()

gibbon_main =
    if eqBenchProg "seqbuildkdtree"
    then bench_seqbuildkdtree
    else if eqBenchProg "seqcountcorr"
    then bench_seqcountcorr
    else if eqBenchProg "seqnearest"
    then bench_seqnearest
    else if eqBenchProg "seqbuildquadtree"
    then bench_seqbuildquadtree
    else if eqBenchProg "seqbhut"
    then bench_seqbhut
    else if eqBenchProg "seqfoldconstants"
    then bench_seqfoldconstants
    else printsym (quote "benchrunner: select benchmark to run with --bench-prog\n")
