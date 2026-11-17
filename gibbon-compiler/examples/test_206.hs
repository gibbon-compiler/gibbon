module Main where

-- Regression test for issue #206: an if-expression of packed type as the
-- right-hand side of a let.

data Tree = Leaf Int
          | Node Tree Tree

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node l r -> sumTree l + sumTree r

-- Constructor branches.
build :: Int -> Tree
build n =
  let c = if n > 5 then Node (Leaf n) (Leaf n) else Leaf 7 in
  c

-- Variable branches. Both variables are used again afterwards, so the
-- branch that is not taken must not clobber them.
pick :: Int -> Int
pick n =
  let a = Leaf 1 in
  let b = Leaf 7 in
  let c = if n == 1 then a else b in
  sumTree a + sumTree b + sumTree c

gibbon_main :: Int
gibbon_main =
  let x = Leaf 3 in
  let y = if sumTree x == 3 then Leaf 10 else Leaf 20 in
  sumTree (build 10) + sumTree (build 1) + pick 1 + pick 0 + sumTree y
