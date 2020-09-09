module ParNearest where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius = intToFloat n
        tr     = fromList_seq pts
        nns = iterate (allNearest_par tr pts)
        -- _ = printVec (\p -> printPoint p) nns
    in sumKdTree tr
