module Poly1 where

data Maybe z = Nothing | Just z
  deriving Show

pureMaybe :: a -> Maybe a
pureMaybe x = Just x

fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe f mb =
  case mb of
    Nothing -> Nothing
    Just x  -> Just (f x)

data Either a b = Left a | Right b
  deriving Show

pureEither :: b -> Either a b
pureEither x = Right x

fmapEither :: (a -> b) -> Either x a -> Either x b
fmapEither f e =
  case e of
    Left x -> Left x
    Right y  -> Right (f y)

data List a = Nil
            | Cons a (List a)
  deriving Show

{-

Bugs:

(1) In the Cons case,

    f x (foldr f acc rst)

.. doesn't work right now. The specializer is not able to lift 'f' out of this expression.

-}
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

id1 :: a -> a
id1 x = x

foo1 :: a -> b -> b
foo1 x y = y

bar :: a -> b -> a
bar x y = foo1 y x

baz :: Int -> Int -> Int
baz x y = x + y

succ :: Int -> Int
succ x = x + 1

isEven :: Int -> Bool
isEven i = (mod i 2) == 0

minus1 :: Int -> Int
minus1 x = x - 1

not :: Bool -> Bool
not b = if b then False else True

dot :: (b -> c) -> (a -> b) -> a -> c
dot f g x = f (g x)

ap :: (a -> b) -> a -> b
ap f x = f x

test_rec :: (a -> b) -> Int -> Int
test_rec f n = if n == 0
           then n
           else test_rec f (n-1)

gibbon_main =
       let
         id2 :: a -> a
         id2 x = x

         -- foo2 :: a -> b -> b
         foo2 x y = y

         x :: Maybe Int
         x = Nothing

         w :: Either Int Int
         w = pureEither 20

         w1 :: Either Int Bool
         w1 = fmapEither isEven w

         v :: Int
         v = dot (plus 1) (plus 1) 10

         u :: Bool
         u = ap not True

         t :: Int
         t = test_rec (plus 1) v

         s :: Int
         s = foldr plus 0 (Cons 1 (Cons 2 Nil))

         r :: List Int
         r = map id1 (Cons 1 (Cons 2 Nil))

         q :: List Int
         q = map2 id1 (Cons 1 (Cons 2 Nil))

         p :: Either Int Bool
         p = ap id2 w1

         o = map (plus 10) (Cons 1 (Cons 2 Nil))

         test = (id1 10, id1 True, id2 11, id2 False, foo1 1 2, foo2 3 4,
                 x, w, w1, v, u, t, s, r, q, p, o)
       in test

main :: IO ()
main = print gibbon_main

{-

ScopedTyVars needs the forall.

goo =
      let foo :: forall a b. (a,b) -> b
          foo arg = let y :: b
                        y = snd arg
                    in y
      in 10

-}
