module SeqBuildKd where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (fromList_seq pts)
    in check_buildkdtree pts tr
