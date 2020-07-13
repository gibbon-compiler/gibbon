module SeqBuildFib where

import BinTree

gibbon_main =
  let n = sizeParam
      x = iterate (mkTreeFib_seq n)
  in (sumTree_seq x)
