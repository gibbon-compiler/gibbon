module SeqBuild3D where

import KdTree

gibbon_main =
    let pts :: [(Float, Float, Float)]
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (fromList_seq pts)
    in sumKdTree tr
