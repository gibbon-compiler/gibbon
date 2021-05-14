module Main where

gibbon_main =
    let a = eqBenchProg "hello"
        b = eqsym (quote "hello") (quote "hello")
    in (a,b)
