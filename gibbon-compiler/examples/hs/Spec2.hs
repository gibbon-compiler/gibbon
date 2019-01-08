-- Test specialization

-- Not supported yet :(
-- import Prelude

module Spec1 where

foo :: a -> b -> a -> a
foo x y z = x

bar :: a -> b -> a
bar x y = foo x y x

baz :: Int -> Int -> Int
baz x y = x + y

data Maybe a = Nothing | Just a

fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe f mb =
  case mb of
    Nothing -> Nothing
    Just x  -> Just (f x)

succ :: Int -> Int
succ x = x + 1

main =
    let
        v1 :: Int
        v1 = bar 10 False

        id2 :: a -> a
        id2 x = x

        v2 :: Maybe Int
        v2 = Just 10

    in (v1 + id2 10 + baz 10 20, fmapMaybe succ v2, id2 True)
