module Main where

data Tree = Leaf Int
          | Node Tree Tree


gibbon_main :: Int
gibbon_main =
    let a = Leaf 123
        c = Node a a
        _ = printPacked c
      in 99999
