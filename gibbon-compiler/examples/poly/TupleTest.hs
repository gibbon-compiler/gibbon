module T1 where

import Prelude hiding (id, map)

id :: a -> a
id x = x

data List a = Nil
            | Cons a (List a)
  deriving Show

map :: (a -> b) -> List a -> List b
map f ls =
  case ls of
    Nil        -> Nil
    Cons x rst -> Cons (f x) (map f rst)

compute :: (List Int,List Int,List Int)
compute =
  let x = map (\x -> x + 1) (Cons 1 (Cons 2 Nil))
      y = map (\x -> 42) x
      z = map id y
  in (x,y,z)

gibbon_main =
  let (x,y,z) = compute
  in case z of
       Nil        -> 0
       Cons x rst -> x
