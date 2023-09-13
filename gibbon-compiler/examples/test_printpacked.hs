module Main where

import Gibbon.Prelude

data Tree = Leaf Int | Node Tree Tree

rightmost :: Tree -> Int
rightmost tr =
    case tr of
        Leaf i -> i
        Node l r -> rightmost r

mkTree :: Int -> Tree
mkTree i =
  if i <= 0
  then Leaf 1
  else
      let x = mkTree (i-1)
          y = mkTree (i-1)
      in Node x y

gibbon_main =
    let v = mkTree 2
        _ = printPacked v
        _ = print_newline()
        w = copyPacked v
        _ = printPacked w
        _ = print_newline()
        x = rightmost v
        _ = printint x
        _ = print_newline()
    in ()
