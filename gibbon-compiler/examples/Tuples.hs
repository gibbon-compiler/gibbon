module Tuples where

foo :: (Int, Int) -> (Int, Int)
foo x = (10, 20)

gibbon_main =
    let v1 = (50, 60)
    in foo v1
