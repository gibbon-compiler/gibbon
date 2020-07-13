module ParBuildFib where

import BinTree

gibbon_main =
  let n = sizeParam
      cutoff = 8
      x = iterate (mkTreeFib_par cutoff n)
  in (sumTree_seq x)
