module NeedsClosure where

ap :: (a -> b) -> a -> b
ap fn arg = fn arg

id :: a -> a
id x = x

ap2 :: (a -> b) -> a -> b
ap2 fn arg = ap (\arg -> fn arg) arg

data MyList a = Nil
              | Cons a (MyList a)
  deriving Show

foldr :: (a -> b -> b) -> b -> MyList a -> b
foldr f acc ls =
  case ls of
    Nil        -> acc
    Cons x rst -> let acc' = (foldr f acc rst)
                  in f x acc'

map :: (a -> b) -> MyList a -> MyList b
map f ls = foldr (\x acc -> Cons (f x) acc) Nil ls

sumMyList :: MyList Int -> Int
sumMyList ls = foldr (\i acc -> i + acc) 0 ls

gibbon_main =
    let m = 10
        n = ap2 (\_ -> m) 10
        o = ap2 id 10
        ls1 = Cons 1 (Cons 2 (Cons 3 Nil))
        ls2 = map (\x -> x + 1) ls1
        p = sumMyList ls2
    in n + o + p
