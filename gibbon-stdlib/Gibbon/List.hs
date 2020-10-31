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
