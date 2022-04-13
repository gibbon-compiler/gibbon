{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Gibbon.List where

import Gibbon.Prelude

append_ll :: List a -> List a -> List a
append_ll l1 l2 =
  if is_empty_ll l1
  then l2
  else
    let hd = head_ll l1
        tl = tail_ll l1
    in cons_ll hd (append_ll tl l2)

foldl_ll :: (b -> a -> b) -> b -> List a -> b
foldl_ll f acc ls =
  if is_empty_ll ls
  then acc
  else
    let hd = head_ll ls
        tl = tail_ll ls
    in foldl_ll f (f acc hd) tl

ifoldl_ll :: (b -> Int -> a -> b) -> b -> List a -> b
{-# INLINE ifoldl_ll #-}
ifoldl_ll f acc ls = ifoldl_ll_loop 0 f acc ls

ifoldl_ll_loop :: Int -> (b -> Int -> a -> b) -> b -> List a -> b
ifoldl_ll_loop idx f acc ls =
  if is_empty_ll ls
  then acc
  else
    let hd = head_ll ls
        tl = tail_ll ls
    in ifoldl_ll_loop (idx+1) f (f acc idx hd) tl

map_ll :: (a -> b) -> List a -> List b
map_ll f ls =
  if is_empty_ll ls
  then let em :: List b
           em = alloc_ll
       in em
  else
    let hd = head_ll ls
        tl = tail_ll ls
    in cons_ll (f hd) (map_ll f tl)


length_ll :: List a -> Int
length_ll ls = foldl_ll (\acc elt -> acc+1) 0 ls

splitAt_ll :: Int -> List a -> (List a, List a)
splitAt_ll n ls 
  = if n ==0 then (alloc_ll, ls)
   else 
     let (a, b) = splitAt_ll (n-1) (tail_ll ls)
     in (cons_ll (head_ll ls) a, b)