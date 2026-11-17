module Main where

-- Regression test for issue #307: a packed value shared between the fields of
-- a constructor, both in the main expression and in a function body.

data Tree = Leaf Int
          | Node Tree Tree

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node l r -> sumTree l + sumTree r

fun :: Int -> Tree
fun n =
  let a = Leaf n in
  let c = Node a a in
  c

gibbon_main :: Int
gibbon_main =
  let a = Leaf 123 in
  let c = Node a a in
  sumTree c + sumTree (fun 1)
