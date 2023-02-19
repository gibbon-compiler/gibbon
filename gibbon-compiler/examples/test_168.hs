data Foo = A (Int, (Int, Int)) | B Int deriving Show
data PList a = Nil | Cons a (PList a) deriving Show

head :: PList a -> a
head a = case a of
  Cons x xs -> x

map :: (a -> b) -> PList a -> PList b
map f a = case a of
  Nil       -> Nil
  Cons x xs -> Cons (f x) (map f xs)

tail :: PList a -> PList a
tail a = case a of
  Nil -> Nil
  Cons z zs -> zs

transpose :: PList (PList a) -> PList (PList a)
transpose a = case a of
  Nil -> Nil
  Cons aa bb -> case aa of
    Nil -> Nil
    Cons _a _b -> Cons (map head a) (transpose (map tail a))

test :: PList (PList ((Int, Foo, Int), (Int, Foo, Int)))
-- >>> transpose xs
-- Cons (Cons ((1,A (6,(7,8)),4),(3,B 8,5)) Nil) Nil
test = Cons (Cons ((1, A (6, (7, 8)), 4),(3, B 8, 5)) Nil) Nil

gibbon_main :: ()
gibbon_main = 
  let _ = transpose test   
  in ()