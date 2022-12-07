module BenchCopyFns where

import KdTree
import Reverse
import TreeUpdate

--------------------------------------------------------------------------------

benchcopyList :: ()
benchcopyList =
  let ls = buildList sizeParam
      ls2 = iterate (copyPList ls)
  in ()

benchevacList :: ()
benchevacList =
  let ls = buildList sizeParam
      -- replace with call to GC by hand.
      ls2 = iterate (copyPList ls)
  in ()

benchcopyTree :: ()
benchcopyTree =
  let ls = buildList sizeParam
      ls2 = iterate (copyPList ls)
  in ()

benchevacTree :: ()
benchevacTree =
  let ls = buildList sizeParam
      -- replace with call to GC by hand.
      ls2 = iterate (copyPList ls)
  in ()

benchcopyKdtree :: ()
benchcopyKdtree =
  let pts :: Vector (Float, Float, Float)
      pts = readArrayFile Nothing
      tr = mkKdTree_seq pts
      tr2 = iterate (copy_kdtree tr)
  in ()

benchevacKdtree :: ()
benchevacKdtree =
  let pts :: Vector (Float, Float, Float)
      pts = readArrayFile Nothing
      tr = mkKdTree_seq pts
      -- replace with call to GC by hand.
      tr2 = iterate (copy_kdtree tr)
  in ()

gibbon_main =
    if eqBenchProg "list"
    then let _ = benchcopyList
             _ = benchevacList
         in ()
    else if eqBenchProg "tree"
    then let _ = benchcopyTree
             _ = benchevacTree
         in ()
    else let _ = benchcopyKdtree
             _ = benchevacKdtree
         in ()
