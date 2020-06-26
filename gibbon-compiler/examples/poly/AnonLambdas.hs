module T1 where

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

compute :: Int -> List Int
compute _ =
  let x = map (\a -> a + 1) (Cons 1 (Cons 2 Nil))
      y = map (\_ -> 42) x
      z = map id y
  in z

gibbon_main =
  let z = compute 10
  in case z of
       Nil      -> 0
       Cons x _ -> x
