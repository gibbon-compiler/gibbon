{-# LANGUAGE ScopedTypeVariables #-}

-- | A module to test various parts of the HS frontend parser, and other parts
-- of the L0 pipeline.
module Tests where

id :: a -> a
id x = x

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
    Just x  -> (f x)
    Nothing -> Nothing

main = let foo :: a -> a
           foo x = if True then x else x

           hoo :: Int
           hoo = ap (\(x :: Int) -> x) 10

       in foo 10
