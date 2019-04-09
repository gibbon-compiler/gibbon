module CurriedFns where

import Prelude hiding (foldr, map)

data List a = Nil
            | Cons a (List a)
  deriving Show

foldr :: (a -> b -> b) -> b -> List a -> b
foldr f acc ls =
  case ls of
    Nil        -> acc
    Cons x rst -> let acc' = (foldr f acc rst)
                  in f x acc'
map :: (a -> b) -> List a -> List b
map f ls =
  case ls of
    Nil        -> Nil
    Cons x rst -> Cons (f x) (map f rst)

map2 :: (a -> b) -> List a -> List b
map2 f ls = foldr (\x acc -> Cons (f x) acc) Nil ls

plus :: Int -> Int -> Int
plus a b = a + b

gibbon_main =
  let x = map (plus 10) (Cons 1 (Cons 2 Nil))
      y = map2 (plus 10) (Cons 1 (Cons 2 Nil))
  in (x,y)
