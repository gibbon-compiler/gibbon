module SeqFib where

import Fib

gibbon_main =
    let n = sizeParam
    in iterate (fib_seq n)
