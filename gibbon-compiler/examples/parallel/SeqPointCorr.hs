module SeqPointCorr where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius  = intToFloat n
        tr      = fromList_seq pts
        tup =  iterate (let i     = rand
                            j     = (mod i n) - 1
                            probe = nth pts j
                            corr = countCorr_seq probe radius tr
                        in (probe, corr))
        (query, actual) = tup
    in check_countcorr pts query actual radius
