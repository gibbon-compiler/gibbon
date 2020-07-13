module ParFib where

import Fib

gibbon_main =
    let n = sizeParam
    in iterate (fib_par 19 n)
