module SeqBuildKd where

import KdTree

gibbon_main =
    let pts :: Vector (Float, Float, Float)
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (fromList_seq pts)
        p = sumList pts
        q = sumKdTree tr
        err = (q .-. p)
        _ = printsym (quote "Err: ")
        _ = printfloat err
        _ = printsym (quote "\n")
        c = countLeaves tr
    in c
