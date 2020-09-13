module SeqNearest where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius = intToFloat n
        tr     = fromList_seq pts
        nns = iterate (allNearest_seq tr pts)
    in check_nearest pts nns radius
