module Lcss where

import Gibbon.Vector
import Gibbon.Prelude
import Gibbon.PList

--------------------------------------------------------------------------------

zip0 :: PList Int -> PList (Int, Int)
zip0 ls =
  case ls of
    Nil -> Nil
    Cons x xs -> Cons (x,0) (zip0 xs)

algb :: PList Int -> PList Int -> PList Int
algb xs ys = Cons 0 (algb1 xs (zip0 ys))

algb1 :: PList Int -> PList (Int, Int) -> PList Int
algb1 xs ys =
  case xs of
    Nil -> map_plist (\(x,y) -> y) ys
    Cons a as ->
      algb1 as (algb2 a 0 0 ys)

algb2 :: Int -> Int -> Int -> PList (Int, Int) -> PList (Int, Int)
algb2 x k0j1 k1j1 ls =
  case ls of
    Nil -> Nil
    Cons a as ->
      let (y,k0j) = a
      in let kjcurr = if x == y
                      then k0j1+1
                      else maxInt k1j1 k0j
         in Cons (y,kjcurr) (algb2 x k0j kjcurr as)

algc :: Int -> Int -> PList Int -> PList Int -> PList Int -> PList Int
algc m n xs ys zs =
  if is_empty_plist ys
  then zs
  else case xs of
         Nil -> Nil
         Cons x xs' ->
           case xs' of
             Nil -> if elem_plist compare_int x ys
                    then Cons x (copyPacked zs)
                    else (copyPacked zs)
             Cons x' xs'' ->
               let m2 = m / 2
                   xs1 = take_plist m2 xs
                   xs2 = drop_plist m2 xs
                   l1 = algb xs1 ys
                   rev_xs2 = reverse_plist xs2 Nil
                   rev_ys = reverse_plist ys Nil
                   l2_0 = algb rev_xs2 rev_ys
                   l2 = reverse_plist l2_0 Nil
                   k = findk 0 0 (-1) (zip_plist l1 l2)
                   algc1 = algc (m-m2) (n-k) xs2 (drop_plist k ys) zs
                   algc2 = algc m2 k xs1 (take_plist k ys) algc1
               in algc2

findk :: Int -> Int -> Int -> PList (Int, Int) -> Int
findk k km m ls =
  case ls of
    Nil -> km
    Cons aVal rst ->
      let (x, y) = aVal
      in if ((x + y) >= m)
         then findk (k + 1) k  (x + y) rst
         else findk (k + 1) km m       rst

mkList :: Int -> Int -> Int -> PList Int
mkList start end skipFactor =
  if (start <= end)
  then let rst = mkList (start + skipFactor) end skipFactor
       in Cons start rst
  else Nil

lcss :: PList Int -> PList Int -> PList Int
lcss xs ys = algc (length_plist xs) (length_plist ys) xs ys Nil


check_lcss :: Int -> Int -> Int -> PList Int -> Bool
check_lcss start step end list2 =
  case list2 of
    Nil -> start > end
    Cons x rst ->
      (x == start) && (check_lcss (start+step) step end rst)

bench_lcss :: (Int,Int,Int,Int,Int,Int) -> (Int,Int,Int) -> Bool
bench_lcss opts answer =
  let (start1,step1,end1,start2,step2,end2) = opts

      ls1 = mkList start1 end1 (step1-start1)
      -- _ = printPacked ls1
      -- _ = print_newline()

      ls2 = mkList start2 end2 (step2-start2)
      -- _ = printPacked ls2
      -- _ = print_newline()

      common = iterate (lcss ls1 ls2)
      -- _ = printPacked common
      -- _ = print_newline()

      (ans_start,ans_step,ans_end) = answer

  in check_lcss ans_start ans_step ans_end common

gibbon_main =
  let n = sizeParam in
    if n < 1 || n == 1
    then bench_lcss test_opts test_opts_answer
    else if n == 2
    then bench_lcss fast_opts fast_opts_answer
    else if n == 3
    then bench_lcss norm_opts norm_opts_answer
    else bench_lcss slow_opts slow_opts_answer

test_opts, fast_opts, norm_opts, slow_opts :: (Int,Int,Int,Int,Int,Int)
test_opts = (1,2,2000,1050,1051,2000)
fast_opts = (1,2,2000,1000,1001,2000)
norm_opts = (1,2,2000,1000,1001,4000)
slow_opts = (1,2,4000,1000,1001,4000)

test_opts_answer, fast_opts_answer, norm_opts_answer, slow_opts_answer :: (Int,Int,Int)
test_opts_answer = (1050,1,2000)
fast_opts_answer = (1000,1,2000)
norm_opts_answer = (1000,1,2000)
slow_opts_answer = (1000,1,4000)
