module ParAdd1Tree where

import BinTree

gibbon_main =
  let n = sizeParam
      x = mkTree_seq n
      cutoff = 19
      y = iterate (add1Tree_par cutoff x)
  in check_add1tree n y
