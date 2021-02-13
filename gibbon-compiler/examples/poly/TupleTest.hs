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

compute :: (MyList Int,MyList Int,MyList Int)
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
