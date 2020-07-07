module SeqCoins where

import Coins

gibbon_main =
    let coins0 :: Vector (Int,Int)
        coins0 = valloc 6
        coins1 = inplacevupdate coins0 0 (250,55)
        coins2 = inplacevupdate coins1 1 (100,88)
        coins3 = inplacevupdate coins2 2 (25,88)
        coins4 = inplacevupdate coins3 3 (10,99)
        coins5 = inplacevupdate coins4 4 (5,122)
        coins6 = inplacevupdate coins5 5 (1,177)
        amt = sizeParam
        tr = iterate (payA_seq amt coins0)
    in lenA tr
