{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Packed lists.
module Gibbon.List where

import Gibbon.Prelude

--------------------------------------------------------------------------------

data PList a = Nil | Cons a (PList a)

elem :: (a -> a -> Int) -> Int -> Plist a -> Bool
elem cmp a list =
  case list of
    Nil       -> False
    Cons x rst -> if (cmp x a) == 0
                   then True
                   else (False || elem cmp a rst)

length :: PList a -> Int
length a = case a of
  Nil       -> 0
  Cons x xs -> 1 + length xs

filter :: (a -> Bool) -> PList a -> PList a
filter f a =
  case a of
    Nil -> Nil
    Cons z zs -> if f z then Cons z (filter f zs) else filter f zs

take :: Int -> PList a -> PList a
take n a =
  if n == 0
    then Nil
  else
    case a of
      Nil -> Nil
      Cons z zs -> Cons z (take (n-1) zs)

drop :: Int -> Plist a -> Plist a
drop num list =
  case list of
    Nil        -> Nil
    Cons x rst -> if (num <= 0)
                   then Cons x rst
                   else drop (num - 1) rst

reverse :: PList a -> PList a -> PList a
reverse xs acc =
  case xs of
    Nil       -> acc
    Cons z zs -> reverse zs (Cons z acc)

map :: (a -> b) -> PList a -> PList b
map f ls =
  case ls of
    Nil -> Nil
    Cons x xs -> Cons (f x) (map f cs)

splitAt :: Int -> PList a -> (PList a, PList a)
splitAt n a = if n == 0
  then (Nil, a)
  else case a of
    Nil       -> (Nil, Nil) -- error case
    Cons x xs -> let (c, d) = splitAt (n - 1) xs in (Cons x c, d)

zip :: PList a -> PList b -> PList (a, b)
zip as bs =
  case as of
    Nil -> Nil
    Cons z zs -> case bs of
      Nil -> Nil
      Cons y ys -> Cons (z, y) (zip zs ys)
