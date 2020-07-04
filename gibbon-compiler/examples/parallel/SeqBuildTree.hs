module SeqBuildTree where

import BinTree

gibbon_main =
  let n = sizeParam
      x = iterate (mkTree_seq n)
  in (sumTree_seq x)
