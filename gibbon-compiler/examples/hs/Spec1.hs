-- Test specialization

-- Not supported yet :(
-- import Prelude

module Spec1 where

foo :: a -> b -> a -> a
foo x y z = x

bar :: a -> b -> a
bar x y = foo x y x

baz :: a -> b -> a
baz x y = bar x y

ap :: (a -> b) -> a -> b
ap f x = f x

dot :: (b -> c) -> (a -> b) -> a -> c
dot f g x = f (g x)

data Maybe a = Nothing | Just a

onlyNothing :: a -> Maybe b
onlyNothing x = Nothing

pureMaybe :: a -> Maybe a
pureMaybe x = Just x

fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe f mb =
  case mb of
    Nothing -> Nothing
    Just x  -> Just (f x)

-- data Either a b = Left a | Right b

-- fmapEither :: (a -> b) -> Either s a -> Either s b
-- fmapEither f eh =
--   case eh of
--     Left  a -> Left a
--     Right b -> Right (f b)

main =
    let
        v1 :: Int
        v1 = baz 10 False

        v2 :: Int
        v2 = ap (\(x::Int) -> x + 1) 10

        succ :: Int -> Int
        succ x = x + 1

        v3 :: Int
        v3 = succ 10

        v4 :: Maybe Int
        v4 = Just 10

        v5 :: Maybe Int
        v5 = Nothing

        v6 :: Maybe Int
        v6 = fmapMaybe (\(x::Int) -> x + 1) v4

        id2 :: a -> a
        id2 x = x

    in (v1 + id2 10, id2 True)
