-- Spine: Tree (Factored) used as a list of trees.  bumpSpine shares every
-- element: one factored indirection per spine node, across many chunks.

module Spine where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))

-- A right spine whose left children are the elements.
mkSpine :: Int -> Tree
mkSpine n = if n <= 0 then Leaf 0 else Node (mkTree n (mod n 4)) (mkSpine (n - 1))

-- Shares every element: one indirection per spine node.
bumpSpine :: Tree -> Tree
bumpSpine t = case t of
  Leaf x -> Leaf (x + 1)
  Node e rest -> Node e (bumpSpine rest)

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> mod x 1000
  Node a b -> sumTree a + (3 * sumTree b)

sumSpine :: Tree -> Int
sumSpine t = case t of
  Leaf x -> x
  Node e rest -> mod ((7 * sumTree e) + (5 * sumSpine rest)) 1000000007

gibbon_main = sumSpine (bumpSpine (bumpSpine (mkSpine 4000)))
