module Benchrunner where

import Fib
import BinTree
import KdTree
import Bhut
import Coins
import Countnodes
import Ray
import FoldConstants

--------------------------------------------------------------------------------

prog_is :: Sym -> Bool
prog_is prog =
    let s = benchProgParam
    in eqsym s prog

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
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (mkKdTree_seq pts)
    in check_buildkdtree pts tr

bench_parbuildkdtree :: ()
bench_parbuildkdtree =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        -- cutoff  = 524288
        cutoff  = 100000
        tr      = iterate (mkKdTree_par cutoff pts)
    in check_buildkdtree pts tr

bench_seqcountcorr :: ()
bench_seqcountcorr =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius  = 100.0
        tr      = mkKdTree_seq pts
--         tup =  iterate (let i     = rand
--                             j     = (mod i n) - 1
--                             probe = nth pts j
--                             corr = countCorr_seq probe radius tr
--                         in (probe, corr))
--         (query, actual) = tup
--     in check_countcorr pts query actual radius

--         (qx, qy, qz, count) = iterate (nCountCorr_seq 1 radius pts tr)
--     in check_countcorr pts (qx,qy,qz) count radius
        pts' = slice 0 n pts
        counts = iterate (allCountCorr_seq radius tr pts')
        query = nth pts' 4
        count = nth counts 4
    in check_countcorr pts query count radius

bench_parcountcorr :: ()
bench_parcountcorr =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius  = 100.0
        tr      = mkKdTree_seq pts
        cutoff  = 524288
--         tup =  iterate (let i     = rand
--                             j     = (mod i n) - 1
--                             probe = nth pts j
--                             corr = countCorr_par cutoff probe radius tr
--                         in (probe, corr))
--         (query, actual) = tup
--     in check_countcorr pts query actual radius
--         (qx, qy, qz, count) = iterate (nCountCorr_par cutoff 1 radius pts tr)
--     in check_countcorr pts (qx,qy,qz) count radius
        pts' = slice 0 n pts
        counts = iterate (allCountCorr_par cutoff radius tr pts')
        query = nth pts' 4
        count = nth counts 4
    in check_countcorr pts query count radius

bench_seqnearest :: ()
bench_seqnearest =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        tr     = mkKdTree_seq pts
        nns = iterate (allNearest_seq tr pts)
    in check_nearest pts nns

bench_parnearest :: ()
bench_parnearest =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        tr     = mkKdTree_seq pts
        nns = iterate (allNearest_par tr pts)
     in check_nearest pts nns

bench_seqbuildquadtree :: ()
bench_seqbuildquadtree =
  let pts :: Vector (Float, Float)
      pts = readArrayFile ()
      particles  = map (\(pt :: (Float, Float)) ->
                            let x = pt !!! 0
                                y = pt !!! 1
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let x = pt !!! 0
                          y = pt !!! 1
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 0) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 1) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 0) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 1) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      tr = iterate (buildQtree_seq box mpts)
  in check_buildquadtree mpts tr

bench_parbuildquadtree :: ()
bench_parbuildquadtree =
  let pts :: Vector (Float, Float)
      pts = readArrayFile ()
      particles  = map (\(pt :: (Float, Float)) ->
                            let x = pt !!! 0
                                y = pt !!! 1
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let x = pt !!! 0
                          y = pt !!! 1
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 0) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 1) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 0) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 1) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      cutoff = 524288
      tr = iterate (buildQtree_par cutoff box mpts)
  in check_buildquadtree mpts tr

bench_seqbhut :: ()
bench_seqbhut =
  let pts :: Vector (Float, Float)
      pts = readArrayFile ()

      particles  = map (\(pt :: (Float, Float)) ->
                            let x = pt !!! 0
                                y = pt !!! 1
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let x = pt !!! 0
                          y = pt !!! 1
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 0) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 1) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 0) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 1) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      bht = buildQtree_seq box mpts
      particles1 = oneStep_seq bht mpts particles
  in check_bhut particles particles1

bench_parbhut :: ()
bench_parbhut =
  let pts :: Vector (Float, Float)
      pts = readArrayFile ()

      particles  = map (\(pt :: (Float, Float)) ->
                            let x = pt !!! 0
                                y = pt !!! 1
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let x = pt !!! 0
                          y = pt !!! 1
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 0) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 1) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 0) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 1) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      bht = buildQtree_seq box mpts
      cutoff = 524288
      particles1 = oneStep_par cutoff bht mpts particles
  in check_bhut particles particles1

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
    in check_coins amt tr
    -- in ()

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
    -- in check_coins amt tr
    in ()

bench_seqcountnodes :: ()
bench_seqcountnodes =
  let e = readPackedFile (@Toplvl, ())
      -- to ensure that mmap'd stuff is in memory.
      _ = countNodesSeq e
      n = iterate (countNodesSeq e)
      _ = printint n
      _ = printsym (quote "\n")
  in ()

bench_parcountnodes :: ()
bench_parcountnodes =
  let e = readPackedFile (@Toplvl, ())
      -- to ensure that mmap'd stuff is in memory.
      _ = countNodesPar e
      n = iterate (countNodesPar e)
      _ = printint n
      _ = printsym (quote "\n")
  in ()

bench_seqmkbvh :: ()
bench_seqmkbvh =
  let scene = rgbbox ()
      spheres = get_spheres_scene scene
      bvh = iterate (mkBvh_seq spheres)
  in ()

bench_parmkbvh :: ()
bench_parmkbvh =
  let scene = rgbbox ()
      spheres = get_spheres_scene scene
      bvh = iterate (mkBvh_par spheres)
  in ()

bench_seqray :: ()
bench_seqray =
  let scene = rgbbox ()
      spheres = get_spheres_scene scene
      size = sizeParam
      width = size
      height = size
      bvh = mkBvh_seq spheres
      cam = camera_from_scene width height scene
      pixels = iterate (render_seq bvh width height cam)
  in ()

bench_parray :: ()
bench_parray =
  let scene = rgbbox ()
      spheres = get_spheres_scene scene
      size = sizeParam
      width = size
      height = size
      bvh = mkBvh_seq spheres
      cam = camera_from_scene width height scene
      pixels = iterate (render_par bvh width height cam)
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
    if prog_is (quote "seqfib")
    then bench_seqfib
    else if prog_is (quote "parfib")
    then bench_parfib
    else if prog_is (quote "seqbuildfib")
    then bench_seqbuildfib
    else if prog_is (quote "parbuildfib")
    then bench_parbuildfib
    else if prog_is (quote "seqbuildtree")
    then bench_seqbuildtree
    else if prog_is (quote "parbuildtree")
    then bench_parbuildtree
    else if prog_is (quote "seqadd1tree")
    then bench_seqadd1tree
    else if prog_is (quote "paradd1tree")
    then bench_paradd1tree
    else if prog_is (quote "seqsumtree")
    then bench_seqsumtree
    else if prog_is (quote "parsumtree")
    then bench_parsumtree
    else if prog_is (quote "seqbuildkdtree")
    then bench_seqbuildkdtree
    else if prog_is (quote "parbuildkdtree")
    then bench_parbuildkdtree
    else if prog_is (quote "seqcountcorr")
    then bench_seqcountcorr
    else if prog_is (quote "parcountcorr")
    then bench_parcountcorr
    else if prog_is (quote "seqnearest")
    then bench_seqnearest
    else if prog_is (quote "parnearest")
    then bench_parnearest
    else if prog_is (quote "seqbuildquadtree")
    then bench_seqbuildquadtree
    else if prog_is (quote "parbuildquadtree")
    then bench_parbuildquadtree
    else if prog_is (quote "seqbhut")
    then bench_seqbhut
    else if prog_is (quote "parbhut")
    then bench_parbhut
    else if prog_is (quote "seqcoins")
    then bench_seqcoins
    else if prog_is (quote "parcoins")
    then bench_parcoins
    else if prog_is (quote "seqcountnodes")
    then bench_seqcountnodes
    else if prog_is (quote "parcountnodes")
    then bench_parcountnodes
    else if prog_is (quote "seqmkbvh")
    then bench_seqmkbvh
    else if prog_is (quote "parmkbvh")
    then bench_parmkbvh
    else if prog_is (quote "seqray")
    then bench_seqray
    else if prog_is (quote "parray")
    then bench_parray
    else if prog_is (quote "seqfoldconstants")
    then bench_seqfoldconstants
    else if prog_is (quote "parfoldconstants")
    then bench_parfoldconstants
    else printsym (quote "benchrunner: select benchmark to run with --bench-prog\n")
