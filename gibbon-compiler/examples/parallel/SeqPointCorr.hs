module SeqPointCorr where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius  = intToFloat n
        tr      = fromList_seq pts
    in iterate (let i     = rand
                    j     = (mod i n) - 1
                    probe = nth pts j
                in countCorr_seq probe radius tr)
