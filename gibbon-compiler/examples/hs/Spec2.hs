-- Test the polymorphic frontend.

-- Imports not supported yet :(
-- import Prelude

module Spec2 where

foo :: a -> b -> a -> a
foo x y z = x

bar :: a -> b -> a
bar x y = foo x y x

baz :: Int -> Int -> Int
baz x y = x + y

test_rec1 :: (a -> a) -> Int -> Int
test_rec1 f x = if x == 0
                then x
                else test_rec1 f (x - 1)

succ :: Int -> Int
succ x = x + 1

minus :: Int -> Int
minus x = x - 1

not :: Bool -> Bool
not b = if b then False else True

dot :: (b -> c) -> (a -> b) -> a -> c
dot f g x = f (g x)

ap :: (a -> b) -> a -> b
ap f x = f x

data Maybe a = Nothing | Just a

fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe f mb =
  case mb of
    Nothing -> Nothing
    Just x  -> Just (f x)

main =
    let
        v1 :: Int
        v1 = bar 10 False

        id2 :: a -> a
        id2 x = x

        v2 :: Maybe Int
        v2 = Just 10

        v3 :: Maybe Bool
        v3 = Just True

        v4 :: Int
        v4 = dot succ succ 10

        v5 :: Bool
        v5 = ap not True

        v6 :: Int
        v6 = test_rec1 succ v4

    in (v1 + id2 10 + baz 10 20 + v4 + v6,  v5, id2 True, fmapMaybe succ v2, fmapMaybe not v3)
