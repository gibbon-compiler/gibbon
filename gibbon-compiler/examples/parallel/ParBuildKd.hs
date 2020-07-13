module ParBuildKd where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        -- 2 ^ 19 == 524288
        cutoff  = 524288
        tr      = iterate (fromList_par cutoff pts)
        p = sumList pts
        q = sumKdTree tr
        err = (q .-. p)
        _ = printsym (quote "Err: ")
    in err
