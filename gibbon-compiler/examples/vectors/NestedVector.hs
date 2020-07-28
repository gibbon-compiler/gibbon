module NestedVector where

import Gibbon.Vector

mkNestedVec :: Int -> Vector (Vector (Int, Int))
mkNestedVec n =
    let inner = generate n (\i -> (i,i))
        outer = generate n (\i -> inner)
    in outer

printTup :: (Int, Int) -> ()
printTup tup =
    let a = tup !!! 0
        b = tup !!! 1
        _ = printsym (quote "(")
        _ = printint a
        _ = printsym (quote ",")
        _ = printint b
        _ = printsym (quote ")")
    in ()

sum :: Vector (Int, Int) -> Int
sum vec =
    foldl
      (\acc (elt :: (Int, Int)) ->
           let (x,y) = elt
           in acc + x + y)
      0
      vec

sumNestedVec :: Vector (Vector (Int, Int)) -> Int
sumNestedVec vec =
    foldl
      (\acc elt ->
           let s = sum elt
           in acc + s)
      0
      vec

gibbon_main =
    let vec = mkNestedVec 4
        _ = printVec (\v -> let _ = printVec printTup v
                                _ = printsym (quote "\n")
                            in ())
            vec
        _ = printsym (quote "\n")
    in sumNestedVec vec
