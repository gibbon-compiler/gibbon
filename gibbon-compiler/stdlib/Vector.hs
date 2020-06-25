{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

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

-- -- Work: O(1)
-- -- Span: O(1)
-- v_splitAt :: Int -> Vector a -> (Vector a, Vector a)
-- v_splitAt n vec =
--     -- Copied from Haskell's vector library.
--     let len = v_length vec
--         n'  = max n 0
--         m   = min n' len
--         m'  = max 0 (len - n')
--     in (v_slice 0 m vec, v_slice m m' vec)

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

-- Work: O(n)
-- Span: O(1)
vgenerate_par :: Int -> Int -> (Int -> a) -> Vector a
vgenerate_par cutoff n f =
    let n'  = maxInt n 0
        vec :: Vector a
        vec  = valloc n'
        vec1 = v_generate_par_loop cutoff vec 0 n' f
    in vec1

-- v_select :: Vector a -> Vector a -> Int -> a
-- v_select v1 v2 i =
--     let len = v_length v1 in
--     if i < len
--     then v_nth v1 i
--     else v_nth v2 (i - len)

-- -- Work: O(n)
-- -- Span: O(n)
-- v_append :: Vector a -> Vector a -> Vector a
-- v_append v1 v2 = v_generate
--                      (v_length v1 + v_length v2)
--                      (\i -> v_select v1 v2 i)

-- -- Work: O(n)
-- -- Span: O(1)
-- v_append_par :: Vector a -> Vector a -> Vector a
-- v_append_par v1 v2 = v_generate_par
--                          (v_length v1 + v_length v2)
--                          (\i -> v_select v1 v2 i)

-- -- Work: O(n)
-- -- Span: O(n)
-- v_map :: (a -> b) -> Vector a -> Vector b
-- v_map f vec = v_generate (v_length vec) (\i -> f (v_nth vec i))

-- -- Work: O(n)
-- -- Span: O(1)
-- v_map_par :: (a -> b) -> Vector a -> Vector b
-- v_map_par f vec = v_generate_par (v_length vec) (\i -> f (v_nth vec i))

-- -- Work: O(n)
-- -- Span: O(n)
-- v_update :: Vector a -> Int -> a -> Vector a
-- v_update vec i x = v_generate
--                        (v_length vec)
--                        (\j -> if i == j then x else v_nth vec j)

-- -- Work: O(n)
-- -- Span: O(1)
-- v_update_par :: Vector a -> Int -> a -> Vector a
-- v_update_par vec i x = v_generate_par
--                            (v_length vec)
--                            (\j -> if i == j then x else v_nth vec j)

-- -- Work: O(n)
-- -- Span: O(n)
-- v_foldl :: (a -> b -> b) -> b -> Vector a -> b
-- v_foldl f acc vec =
--     let len = v_length vec in
--     if len == 0
--       then acc
--       else if len == 1
--         then f (v_nth vec 0) acc
--         else v_foldl f (f (v_nth vec 0) acc) (v_slice 1 (len - 1) vec)

-- -- Work: O(n)
-- -- Span: O(log n)
-- v_foldl1_par :: (a -> a -> a) -> a -> Vector a -> a
-- v_foldl1_par f acc vec =
--     let len = v_length vec in
--     if len == 0
--       then acc
--       else if len == 1
--         then f (v_nth vec 0) acc
--         else
--           let mid  = div len 2
--               tup  = v_splitAt mid vec
--               v1   = fst tup
--               v2   = snd tup
--               acc1 = spawn (v_foldl1_par f acc v1)
--               acc2 = (v_foldl1_par f acc v2)
--               _    = sync
--           in f acc1 acc2

-- -- Work: O(n)
-- -- Span: O(log n)
-- v_foldl2_par :: (a -> b -> b) -> b -> (b -> b -> b) -> Vector a -> b
-- v_foldl2_par f acc g vec =
--     let len = v_length vec in
--     if len == 0
--       then acc
--       else if len == 1
--         then f (v_nth vec 0) acc
--         else
--           let mid  = div len 2
--               tup  = v_splitAt mid vec
--               v1   = fst tup
--               v2   = snd tup
--               acc1 = spawn (v_foldl2_par f acc g v1)
--               acc2 = (v_foldl2_par f acc g v2)
--               _    = sync
--           in g acc1 acc2
