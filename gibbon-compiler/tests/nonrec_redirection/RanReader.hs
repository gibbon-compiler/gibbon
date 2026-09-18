module Main where

-- rightVal reaches its right child through a random-access (RAN) pointer and
-- reads it with valOf; both are non-recursive SoA readers. Each parent reads
-- its two children with rightVal before writing itself.
data T = Leaf Int | Node Int T T
{-# ANN type T "Factored" #-}

valOf :: T -> Int
valOf t = case t of
  Leaf x -> x
  Node x _ _ -> x

rightVal :: T -> Int
rightVal t = case t of
  Leaf x -> x
  Node _ _ r -> valOf r

build :: Int -> T
build d =
  if d <= 0
  then Leaf 1
  else let l = build (d - 1)
           r = build (d - 1)
           v = rightVal l + rightVal r + 1
       in Node v l r

sumT :: T -> Int
sumT t = case t of
  Leaf x -> x
  Node x l r -> x + sumT l + sumT r

gibbon_main = sumT (build 16)
