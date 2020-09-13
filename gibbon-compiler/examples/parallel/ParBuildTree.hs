module ParBuildTree where

import BinTree

gibbon_main =
  let n = sizeParam
      cutoff = 19
      tr = iterate (mkTree_par cutoff n)
  in check_buildtree n tr
