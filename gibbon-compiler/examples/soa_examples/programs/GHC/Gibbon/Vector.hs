module Gibbon.Vector
  ( Vector
  , generate
  , nth
  ) where

import Prelude

type Vector a = [a]

generate :: Int -> (Int -> a) -> Vector a
generate n f = go 0 []
  where
    go i acc = if i >= n then reverse acc else go (i + 1) (f i : acc)

nth :: Vector a -> Int -> a
nth xs idx = go xs idx
  where
    go [] _ = error "nth: index out of bounds"
    go (y:ys) i = if i == 0 then y else go ys (i - 1)
