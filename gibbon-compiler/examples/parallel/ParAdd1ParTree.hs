module ParAdd1ParTree where

import BinTree

gibbon_main =
  let n = sizeParam
      cutoff = 19
      x = mkTree_par cutoff n
      y = iterate (add1Tree_par cutoff x)
  in check_add1tree n y
