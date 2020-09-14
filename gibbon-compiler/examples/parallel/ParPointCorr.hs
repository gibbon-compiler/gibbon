module ParPointCorr where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n   = sizeParam
        radius  = intToFloat n
        -- 524288 == 2^19
        cutoff  = 524288
        tr      = fromList_seq pts
        tup =  iterate (let i     = rand
                            j     = (mod i n) - 1
                            probe = nth pts j
                            corr = countCorr_par probe radius tr
                        in (probe, corr))
        (query, actual) = tup
    in check_countcorr pts query actual radius
