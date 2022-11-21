data PList a = Nil | Cons a (PList a) deriving Show

head :: PList p -> p
head a = case a of
  Cons x xs -> x

-- >>> gibbon_main
-- ()

gibbon_main = 
  let xs = Cons (1, ((False, 2), True)) Nil
      _ = head xs
  in ()