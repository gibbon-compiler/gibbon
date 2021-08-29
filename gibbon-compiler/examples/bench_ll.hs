-- Benchmark the primitive malloc'd linked lists to the Packed version.
-- This primarily measures the region allocation performance.
module BenchLL where

import Gibbon.Prelude
import Gibbon.List

--------------------------------------------------------------------------------

loop1 :: Int -> a -> List a -> List a
loop1 n x xs =
  if n == 0
  then xs
  else loop1 (n-1) x (cons_ll x xs)

--------------------------------------------------------------------------------

data PList a = Cons_PList a (PList a)
             | Nil_PList

sumPList :: Int -> PList Int -> Int
sumPList acc ls =
  case ls of
    Nil_PList -> acc
    Cons_PList x xs -> sumPList (acc+x) xs

loop2 :: Int -> a -> PList a -> PList a
loop2 n x xs =
  -- let xs' = copyPacked xs in
  if n == 0
  then xs
  else loop2 (n-1) x (Cons_PList x xs)

--------------------------------------------------------------------------------

gibbon_main =
  let
      xs :: List Int
      xs = alloc_ll
      xs' = iterate (loop1 sizeParam 1 xs)
      n = foldl_ll (\acc v -> acc + v) 0 xs'
      -- n = 10

      ys :: PList Int
      ys = Nil_PList
      ys' = iterate (loop2 sizeParam 1 ys)
      m = sumPList 0 ys'
      _ = printPacked ys'
      _ = print_newline()
  in (n,m)
