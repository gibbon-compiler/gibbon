module SeqBuildTree where

import BinTree

gibbon_main =
  let n = sizeParam
      tr = iterate (mkTree_seq n)
  in check_buildtree n tr
