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

main = let foo :: a -> a
           foo x = if True then x else x

       in foo 10
