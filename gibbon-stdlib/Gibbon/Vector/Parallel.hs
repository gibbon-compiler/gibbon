module Gibbon.Vector.Parallel where

-- -- haskell-src-exts can't parse this.
-- #if MIN_VERSION_GLASGOW_HASKELL(8,4,4,0)
-- import Gibbon.Prim
-- #endif

import Gibbon.Prelude
import Gibbon.Vector

--------------------------------------------------------------------------------

-- Same default as Cilk.
defaultGrainSize :: Int -> Int
{-# INLINE defaultGrainSize #-}
defaultGrainSize n =
    let p = getNumProcessors
        grain = maxInt 1 (div n (8 * p))
    in minInt 2048 grain

generate_par_loop :: Int -> Vector a -> Int -> Int -> (Int -> a) -> Vector a
generate_par_loop cutoff vec start end f =
    if (end - start) <= cutoff
    then generate_loop vec start end f
    else
      let mid  = div (start + end) 2
          vec1 = spawn (generate_par_loop cutoff vec start mid f)
          vec2 = generate_par_loop cutoff vec mid end f
          _    = sync
      in vec2

-- Work: O(n)
-- Span: O(1)
generate_par :: Int -> (Int -> a) -> Vector a
{-# INLINE generate_par #-}
generate_par n f =
    let n'  = maxInt n 0
        vec :: Vector a
        vec  = valloc n'
        cutoff = defaultGrainSize n'
        vec1 = generate_par_loop cutoff vec 0 n' f
    in vec1

-- Work: O(n)
-- Span: O(1)
copy_par :: Vector a -> Vector a
{-# INLINE copy_par #-}
copy_par vec = generate_par (length vec) (\i -> nth vec i)

-- Work: O(n)
-- Span: O(1)
append_par :: Vector a -> Vector a -> Vector a
{-# INLINE append_par #-}
append_par v1 v2 = generate_par
                        (length v1 + length v2)
                        (\i -> select v1 v2 i)

-- Work: O(n)
-- Span: O(1)
map_par :: (a -> b) -> Vector a -> Vector b
{-# INLINE map_par #-}
map_par f vec = generate_par (length vec) (\i -> f (vnth vec i))

-- Work: O(n)
-- Span: O(1)
update_par :: Vector a -> Int -> a -> Vector a
{-# INLINE update_par #-}
update_par vec i x = generate_par
                          (length vec)
                          (\j -> if i == j then x else vnth vec j)

-- Work: O(n)
-- Span: O(log n)
foldl1_par :: (a -> a -> a) -> a -> Vector a -> a
foldl1_par f acc vec =
    let len = length vec in
    if len == 0
      then acc
      else if len == 1
        then f (vnth vec 0) acc
        else
          let mid  = div len 2
              tup  = splitAt mid vec
              v1   = fst tup
              v2   = snd tup
              acc1 = spawn (foldl1_par f acc v1)
              acc2 = (foldl1_par f acc v2)
              _    = sync
          in f acc1 acc2

-- Work: O(n)
-- Span: O(log n)
foldl2_par :: (b -> a -> b) -> b -> (b -> b -> b) -> Vector a -> b
foldl2_par f acc g vec =
    let len = length vec in
    if len == 0
      then acc
      else if len == 1
        then f acc (vnth vec 0)
        else
          let mid  = div len 2
              tup  = splitAt mid vec
              v1   = fst tup
              v2   = snd tup
              acc1 = spawn (foldl2_par f acc g v1)
              acc2 = (foldl2_par f acc g v2)
              _    = sync
          in g acc1 acc2
