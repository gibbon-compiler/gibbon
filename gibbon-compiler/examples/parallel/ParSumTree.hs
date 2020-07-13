module ParSumTree where

import BinTree

gibbon_main =
  let n = sizeParam
      x = mkTree_seq n
      cutoff = 19
      y = iterate (sumTree_par cutoff x)
  in y
