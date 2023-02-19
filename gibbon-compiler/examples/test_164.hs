data PList a = Nil | Cons a (PList a) deriving Show

map :: (a -> b) -> PList a -> PList b
map f a = case a of
  Nil       -> Nil
  Cons x xs -> Cons (f x) (map f xs)
-- >>> gibbon_main
-- Cons 3 (Cons 5 (Cons 7 Nil))
gibbon_main = 
  let f1 x = x + 1 
      f2 x = x * 2 
      ls = Cons 1 (Cons 2 (Cons 3 Nil))
  in  map f1 (map f2 ls)