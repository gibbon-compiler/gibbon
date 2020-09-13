module SeqAdd1Tree where

import BinTree

gibbon_main =
  let n = sizeParam
      x = mkTree_seq n
      y = iterate (add1Tree_seq x)
  in check_add1tree n y
