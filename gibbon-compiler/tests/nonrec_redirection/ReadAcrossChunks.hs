module Main where

-- Each parent reads its two already-built children through the non-recursive
-- reader valOf, then writes itself: val d = 2^d, sumT (build d) = (d+1) * 2^d.
data T = Leaf Int | Node Int T T
{-# ANN type T "Factored" #-}

valOf :: T -> Int
valOf t = case t of
  Leaf x -> x
  Node x _ _ -> x

build :: Int -> T
build d =
  if d <= 0
  then Leaf 1
  else let l = build (d - 1)
           r = build (d - 1)
           v = valOf l + valOf r
       in Node v l r

sumT :: T -> Int
sumT t = case t of
  Leaf x -> x
  Node x l r -> x + sumT l + sumT r

gibbon_main = sumT (build 16)
