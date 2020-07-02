{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

module Gibbon.Vector where

-- A standard library for Gibbon

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

{-
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0)

-- Built-ins. Uncomment this block in order to load this file in GHCi.

data Vector a = Vector

valloc :: Int -> Vector a
valloc = _builtin

vlength :: Vector a -> Int
vlength = _builtin

vnth :: Vector a -> Int -> a
vnth = _builtin

vslice :: Int -- Starting index
        -> Int -- length
        -> Vector a -> Vector a
vslice = _builtin

inplacevupdate :: Vector a -> Int -> a -> Vector a
inplacevupdate = _builtin

numCapabilities :: Int
numCapabilities = _builtin

-- v_inject :: Vector a -> Vector (Int, a) -> Vector a
-- v_inject = _builtin

-- v_ninject_par :: Vector a -> Vector (Int, a) -> Vector a
-- v_ninject_par = _builtin

spawn :: a -> a
spawn = _builtin

sync :: ()
sync = ()

#endif

-}

--------------------------------------------------------------------------------

maxInt :: Int -> Int -> Int
maxInt a b = if a > b then a else b

minInt :: Int -> Int -> Int
minInt a b = if a < b then a else b

--------------------------------------------------------------------------------

-- Work: O(1)
-- Span: O(1)
visEmpty :: Vector a -> Bool
visEmpty vec = vlength vec == 0

-- Work: O(1)
-- Span: O(1)
vsplitAt :: Int -> Vector a -> (Vector a, Vector a)
vsplitAt n vec =
    -- Copied from Haskell's vector library.
    let len = vlength vec
        n'  = maxInt n 0
        m   = minInt n' len
        m'  = maxInt 0 (len - n')
    in (vslice 0 m vec, vslice m m' vec)

v_generate_loop :: Vector a -> Int -> Int -> (Int -> a) -> Vector a
v_generate_loop vec start end f =
    if start == end
    then vec
    else
      let vec1 = inplacevupdate vec start (f start)
      in v_generate_loop vec1 (start+1) end f

-- Work: O(n)
-- Span: O(n)
vgenerate :: Int -> (Int -> a) -> Vector a
vgenerate n f =
    let n'  = maxInt n 0
        vec :: Vector a
        vec = valloc n'
        vec1  = v_generate_loop vec 0 n' f
    in vec1

v_generate_par_loop :: Int -> Vector a -> Int -> Int -> (Int -> a) -> Vector a
v_generate_par_loop cutoff vec start end f =
    if (end - start) <= cutoff
    then v_generate_loop vec start end f
    else
      let mid  = div (start + end) 2
          vec1 = spawn (v_generate_par_loop cutoff vec start mid f)
          vec2 = v_generate_par_loop cutoff vec1 mid end f
          _    = sync
      in vec2

-- Same default as Cilk.
defaultGrainSize :: Int -> Int
defaultGrainSize n =
    let p = getNumProcessors
        grain = maxInt 1 (n / (8 * p))
    in minInt 2048 grain

-- Work: O(n)
-- Span: O(1)
vgenerate_par :: Int -> (Int -> a) -> Vector a
vgenerate_par n f =
    let n'  = maxInt n 0
        vec :: Vector a
        vec  = valloc n'
        cutoff = defaultGrainSize n'
        vec1 = v_generate_par_loop cutoff vec 0 n' f
    in vec1

v_select :: Vector a -> Vector a -> Int -> a
v_select v1 v2 i =
    let len = vlength v1 in
    if i < len
    then vnth v1 i
    else vnth v2 (i - len)

-- Work: O(n)
-- Span: O(n)
vappend :: Vector a -> Vector a -> Vector a
vappend v1 v2 = vgenerate
                    (vlength v1 + vlength v2)
                    (\i -> v_select v1 v2 i)

-- Work: O(n)
-- Span: O(1)
vappend_par :: Vector a -> Vector a -> Vector a
vappend_par v1 v2 = vgenerate_par
                        (vlength v1 + vlength v2)
                        (\i -> v_select v1 v2 i)

-- Work: O(n)
-- Span: O(n)
vmap :: (a -> b) -> Vector a -> Vector b
vmap f vec = vgenerate (vlength vec) (\i -> f (vnth vec i))

-- Work: O(n)
-- Span: O(1)
vmap_par :: (a -> b) -> Vector a -> Vector b
vmap_par f vec = vgenerate_par (vlength vec) (\i -> f (vnth vec i))

-- Work: O(n)
-- Span: O(n)
vupdate :: Vector a -> Int -> a -> Vector a
vupdate vec i x = vgenerate
                      (vlength vec)
                      (\j -> if i == j then x else vnth vec j)

-- Work: O(n)
-- Span: O(1)
vupdate_par :: Vector a -> Int -> a -> Vector a
vupdate_par vec i x = vgenerate_par
                          (vlength vec)
                          (\j -> if i == j then x else vnth vec j)

-- Work: O(n)
-- Span: O(n)
vfoldl :: (b -> a -> b) -> b -> Vector a -> b
vfoldl f acc vec =
    let len = vlength vec in
    if len == 0
      then acc
      else if len == 1
        then f acc (vnth vec 0)
        else vfoldl f (f acc (vnth vec 0)) (vslice 1 (len-1) vec)

-- Work: O(n)
-- Span: O(log n)
vfoldl1_par :: (a -> a -> a) -> a -> Vector a -> a
vfoldl1_par f acc vec =
    let len = vlength vec in
    if len == 0
      then acc
      else if len == 1
        then f (vnth vec 0) acc
        else
          let mid  = div len 2
              tup  = vsplitAt mid vec
              v1   = fst tup
              v2   = snd tup
              acc1 = spawn (vfoldl1_par f acc v1)
              acc2 = (vfoldl1_par f acc v2)
              _    = sync
          in f acc1 acc2

-- Work: O(n)
-- Span: O(log n)
vfoldl2_par :: (b -> a -> b) -> b -> (b -> b -> b) -> Vector a -> b
vfoldl2_par f acc g vec =
    let len = vlength vec in
    if len == 0
      then acc
      else if len == 1
        then f acc (vnth vec 0)
        else
          let mid  = div len 2
              tup  = vsplitAt mid vec
              v1   = fst tup
              v2   = snd tup
              acc1 = spawn (vfoldl2_par f acc g v1)
              acc2 = (vfoldl2_par f acc g v2)
              _    = sync
          in g acc1 acc2
