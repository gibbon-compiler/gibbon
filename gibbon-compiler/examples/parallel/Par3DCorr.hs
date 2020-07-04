module Par3Corr where

import KdTree

-- measure :: [(Float, Float, Float)] -> Int -> Int
-- measure pts n =
--     let radius  = intToFloat n
--         i       = rand
--         j       = (mod i n) - 1
--         probe   = vnth j pts
--         -- 524288 == 2^19
--         cutoff  = 524288
--         tr      = fromList_par cutoff pts
--     in countCorr_par cutoff probe radius tr

gibbon_main =
    let pts :: [(Float, Float, Float)]
        pts = readArrayFile ()
        n   = sizeParam
        radius  = intToFloat n
        i       = rand
        j       = (mod i n) - 1
        probe   = vnth j pts
        -- 524288 == 2^19
        cutoff  = 524288
        tr      = fromList_seq pts
    in iterate (countCorr_par cutoff probe radius tr)
