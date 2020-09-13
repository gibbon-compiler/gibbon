module SeqSumTree where

import BinTree

gibbon_main =
  let n = sizeParam
      x = mkTree_seq n
      y = iterate (sumTree_seq x)
  in check_sumtree n y
