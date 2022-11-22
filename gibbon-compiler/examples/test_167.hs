data PList a = Nil | Cons a (PList a) deriving Show

head :: PList p -> p
head a = case a of
  Cons x xs -> x

-- >>> gibbon_main
-- ()

gibbon_main = 
  let xs = Cons (1, ((False, 2), True)) Nil
      (a, b) = head xs
      (b1, b2) = b 
      (b11, b12) = b1 
  in b12