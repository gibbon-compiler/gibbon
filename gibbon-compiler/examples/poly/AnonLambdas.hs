module T1 where

id :: a -> a
id x = x

data MyList a = Nil
              | Cons a (MyList a)
  deriving Show

map :: (a -> b) -> MyList a -> MyList b
map f ls =
  case ls of
    Nil        -> Nil
    Cons x rst -> Cons (f x) (map f rst)

compute :: Int -> MyList Int
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
