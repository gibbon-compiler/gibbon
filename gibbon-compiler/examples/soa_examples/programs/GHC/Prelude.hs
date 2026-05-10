{-# LANGUAGE PackageImports #-}
module Prelude (module PBase, Div(..), mod, div) where

import qualified "base" Prelude as P
import "base" Prelude as PBase hiding ((/), mod, div)

class Div a where
  (/) :: a -> a -> a

instance Div Int where
  (/) = P.quot

instance Div Integer where
  (/) = P.quot

instance Div Double where
  (/) = (P./)

instance Div Float where
  (/) = (P./)

div :: Int -> Int -> Int
div = P.quot

mod :: Int -> Int -> Int
mod = P.rem
