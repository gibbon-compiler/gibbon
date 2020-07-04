module ParBuildTree where

import BinTree

gibbon_main =
  let n = sizeParam
      cutoff = 19
      x = iterate (mkTree_par cutoff n)
  in (sumTree_seq x)
