module Main where

import Gibbon.Prelude

data Tree = Leaf Int | Node Tree Tree

mkTree :: Int -> Tree
mkTree i =
  if i <= 0
  then Leaf 1
  else
      let x = mkTree (i-1)
          y = mkTree (i-1)
      in Node x y

sumTree :: Tree -> Int
sumTree foo =
  case foo of
    Leaf i     -> i
    Node a b ->
      let x = sumTree a
          y = sumTree b
      in x + y

gibbon_main =
   let v = mkTree sizeParam
       n = sumTree v
       _ = writePackedFile "tree.gpkd" v
       v2 = readPackedFile @Tree (Just "tree.gpkd")
       m = sumTree v2
   in (n,m)
