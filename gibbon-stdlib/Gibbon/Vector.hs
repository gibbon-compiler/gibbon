{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
#if __GLASGOW_HASKELL__ >= 901
{-# LANGUAGE LinearTypes         #-}
#endif

module Gibbon.Vector where

import Gibbon.Prelude

--------------------------------------------------------------------------------
-- Wrappers over Gibbon primitives.

-- Work: O(1)
-- Span: O(1)
alloc :: Int -> Vector a
{-# INLINE alloc #-}
alloc vec = valloc vec

-- Work: O(1)
-- Span: O(1)
length :: Vector a %1-> Int
{-# INLINE length #-}
length vec = vlength vec

-- Work: O(1)
-- Span: O(1)
length1 :: Vector a %1-> Ur Int
{-# INLINE length1 #-}
length1 vec = (unsafeToLinear Ur) (vlength vec)

-- Work: O(1)
-- Span: O(1)
length2 :: Vector a %1-> (Ur Int, Vector a)
{-# INLINE length2 #-}
length2 vec =
    unsafeAlias vec &
      \(vec1,vec2) ->
          ((unsafeToLinear Ur) (vlength vec1), vec2)

-- Work: O(1)
-- Span: O(1)
nth :: Vector a %1-> Int -> a
{-# INLINE nth #-}
nth vec i = vnth vec i

-- Work: O(1)
-- Span: O(1)
nth1 :: Vector a %1-> Int -> Ur a
{-# INLINE nth1 #-}
nth1 vec i = (unsafeToLinear Ur) (vnth vec i)

nth2 :: Vector a %1-> Int -> (Ur a, Vector a)
{-# INLINE nth2 #-}
nth2 vec i =
    unsafeAlias vec &
      \(vec1,vec2) ->
          ((unsafeToLinear Ur) (vnth vec1 i), vec2)


-- Work: O(1)
-- Span: O(1)
slice :: Int -- Starting index
      -> Int -- length
      -> Vector a
      -> Vector a
{-# INLINE slice #-}
slice i n vec = vslice i n vec

-- Work: O(1)
-- Span: O(1)
-- | Unsafe because it aliases the input slice.
unsafeSlice
    ::   Int -- Starting index
    ->   Int -- length
    ->   Vector a
    %1-> Vector a
{-# INLINE unsafeSlice #-}
unsafeSlice i n vec = vslice i n vec

-- Work: O(1)
-- Span: O(1)
merge :: Vector a %1-> Vector a %1-> Vector a
{-# INLINE merge #-}
merge vec1 vec2 = vmerge vec1 vec2

sort :: (a -> a -> Int) -> Vector a %1-> Vector a
{-# INLINE sort #-}
sort cmp vec = vsort vec cmp

flatten :: Vector (Vector a) -> Vector a
{-# INLINE flatten #-}
flatten ls = vconcat ls

inplaceSort :: (a -> a -> Int) -> Vector a %1-> Vector a
{-# INLINE inplaceSort #-}
inplaceSort cmp vec = inplacevsort vec cmp

-- Work: O(1)
-- Span: O(1)
inplaceUpdate :: Int -> a -> Vector a %1-> Vector a
{-# INLINE inplaceUpdate #-}
inplaceUpdate i val vec = inplacevupdate vec i val

--------------------------------------------------------------------------------

-- Work: O(1)
-- Span: O(1)
isEmpty :: Vector a -> Bool
{-# INLINE isEmpty #-}
isEmpty vec = vlength vec == 0

-- Work: O(1)
-- Span: O(1)
singleton :: a -> Vector a
{-# INLINE singleton #-}
singleton x =
    let vec :: Vector a
        vec = valloc 1
        vec2 = inplacevupdate vec 0 x
    in  vec2

-- Work: O(1)
-- Span: O(1)
splitAt :: Int -> Vector a -> (Vector a, Vector a)
{-# INLINE splitAt #-}
splitAt n vec =
    -- Copied from Haskell's vector library.
    let len = vlength vec
        n'  = maxInt n 0
        m   = minInt n' len
        m'  = maxInt 0 (len - n')
    in (vslice 0 m vec, vslice m m' vec)

lsplitAt :: Int -> Vector a %1-> (Ur Int, Vector a,
                                  Ur Int, Vector a)
{-# INLINE lsplitAt #-}
lsplitAt n vec = unsafeToLinear (\x -> lsplitAt' n x) vec

lsplitAt' :: Int -> Vector a -> (Ur Int, Vector a,
                                 Ur Int, Vector a)
{-# INLINE lsplitAt' #-}
lsplitAt' n vec =
    let (x,y) = splitAt n vec
    in (Ur (vlength x), x, Ur (vlength y), y)

{-

lsplitAt :: Int -> Vector a %1-> (Ur Int, Vector a,
                                  Ur Int, Vector a)
{-# INLINE lsplitAt #-}
lsplitAt n vec =
    unsafeAlias vec &
        \(vec1,vec2) ->
            length1 vec1 &
                \(Ur len) ->
                    lsplitAt' n len vec2

lsplitAt' :: Int -> Int -> Vector a %1-> (Ur Int, Vector a,
                                          Ur Int, Vector a)
lsplitAt' n len vec =
    -- Copied from Haskell's vector library.
    let n'  = maxInt n 0
        m   = minInt n' len
        m'  = maxInt 0 (len - n') in
      unsafeAlias vec &
          \(vec1,vec2) ->
              unsafeSlice 0 m vec1 &
                  \sl1 ->
                      unsafeSlice m m' vec2 &
                          \sl2 ->
                              ( Ur m , sl1,
                                Ur m', sl2 )

-}

-- Work: O(1)
-- Span: O(1)
head :: Vector a %1-> a
{-# INLINE head #-}
head vec = nth vec 0

-- Work: O(1)
-- Span: O(1)
tail :: Vector a -> Vector a
{-# INLINE tail #-}
tail vec = slice 1 ((vlength vec)-1) vec

generate_loop :: Vector a -> Int -> Int -> (Int -> a) -> Vector a
generate_loop vec idx end f =
    if idx == end
    then vec
    else
      let vec1 = inplacevupdate vec idx (f idx)
      in generate_loop vec1 (idx+1) end f

-- Work: O(n)
-- Span: O(n)
generate :: Int -> (Int -> a) -> Vector a
{-# INLINE generate #-}
generate n f =
    let n'  = maxInt n 0
        vec :: Vector a
        vec = valloc n'
        vec1 = generate_loop vec 0 n' f
    in vec1

-- Work: O(n)
-- Span: O(n)
copy :: Vector a -> Vector a
{-# INLINE copy #-}
copy vec = generate (vlength vec) (\i -> nth vec i)

lcopy :: Vector a %1-> Vector a
{-# INLINE lcopy #-}
lcopy vec = unsafeToLinear copy vec

select :: Vector a -> Vector a -> Int -> a
{-# INLINE select #-}
select v1 v2 i =
    let len = vlength v1 in
    if i < len
    then vnth v1 i
    else vnth v2 (i - len)

-- Work: O(n)
-- Span: O(n)
append :: Vector a -> Vector a -> Vector a
{-# INLINE append #-}
append v1 v2 = generate
                    (vlength v1 + vlength v2)
                    (\i -> select v1 v2 i)

-- Work: O(n)
-- Span: O(n)
map :: (a -> b) -> Vector a -> Vector b
{-# INLINE map #-}
map f vec = generate (vlength vec) (\i -> f (vnth vec i))

lmap :: (a -> b) -> Vector a %1-> Vector b
lmap f vec = unsafeToLinear (\x -> map f x) vec

-- Work: O(n)
-- Span: O(n)
update :: Vector a -> Int -> a -> Vector a
{-# INLINE update #-}
update vec i x = generate
                      (length vec)
                      (\j -> if i == j then x else vnth vec j)


-- Work: O(n)
-- Span: O(n)
foldl :: (b -> a -> b) -> b -> Vector a -> b
{-# INLINE foldl #-}
foldl f acc vec = foldl_loop 0 (vlength vec) f acc vec

foldl_loop :: Int -> Int -> (b -> a -> b) -> b -> Vector a -> b
foldl_loop idx end f acc vec =
    if idx == end
      then acc
      else
        let acc1 = f acc (vnth vec idx)
        in foldl_loop (idx+1) end f acc1 vec

lfoldl :: (b -> a -> b) -> b -> Vector a %1-> b
{-# INLINE lfoldl #-}
lfoldl f acc vec = unsafeToLinear (\x -> foldl f acc x) vec

-- Work: O(n)
-- Span: O(n)
scanl :: (b -> a -> b) -> b -> Vector a -> Vector b
{-# INLINE scanl #-}
scanl f acc vec =
  let len = vlength vec
      result :: Vector b
      result = valloc len
  in scanl_loop 0 len f acc vec result

scanl_loop :: Int -> Int -> (b -> a -> b) -> b -> Vector a -> Vector b -> Vector b
scanl_loop idx end f acc vec result =
    if idx == end
      then result
      else
        let acc1 = f acc (vnth vec idx)
            result' = inplacevupdate result idx acc1
        in scanl_loop (idx+1) end f acc1 vec result'

lscanl :: (b -> a -> b) -> b -> Vector a -> Vector b
{-# INLINE lscanl #-}
lscanl f acc vec = unsafeToLinear (\x -> scanl f acc x) vec

-- Work: O(n)
-- Span: O(n)
ifoldl :: (b -> Int -> a -> b) -> b -> Vector a -> b
{-# INLINE ifoldl #-}
ifoldl f acc vec = ifoldl_loop 0 (vlength vec) f acc vec

-- Work: O(n)
-- Span: O(n)
ifoldl_loop :: Int -> Int -> (b -> Int -> a -> b) -> b -> Vector a -> b
ifoldl_loop idx end f acc vec =
    if idx == end
      then acc
      else
        let acc1 = f acc idx (vnth vec idx)
        in ifoldl_loop (idx+1) end f acc1 vec

lifoldl :: (b -> Int -> a -> b) -> b -> Vector a %1-> b
{-# INLINE lifoldl #-}
lifoldl f acc vec = unsafeToLinear (\x -> ifoldl f acc x) vec

-- | It returns an Int because Gibbon doesn't have an IO monad yet.
printVec :: (a -> ()) -> Vector a -> ()
printVec f vec =
    let _ = printsym (quote "[")
        _ = printVec_loop 0 (vlength vec) vec f
        _ = printsym (quote "]")
    in ()

printVec_loop :: Int -> Int -> Vector a -> (a -> ()) -> ()
printVec_loop idx end vec f =
    if idx == end
    then ()
    else
        let _ = f (vnth vec idx)
            _ = printsym (quote ",")
        in printVec_loop (idx+1) end vec f

-- Work: O(n)
-- Span: O(n)
snoc :: Vector a -> a -> Vector a
{-# INLINE snoc #-}
snoc vec x =
    let len = vlength vec
        vec2 :: Vector a
        vec2 = valloc (len + 1)
        vec3 = generate_loop vec2 0 len (\i -> nth vec i)
        vec4 = inplacevupdate vec3 len x
    in vec4

lsnoc :: Vector a %1-> a -> Vector a
{-# INLINE lsnoc #-}
lsnoc vec x = unsafeToLinear (\y -> snoc y x) vec

-- Work: O(n)
-- Span: O(n)
cons :: a -> Vector a -> Vector a
{-# INLINE cons #-}
cons x vec =
    let len = vlength vec
        vec2 :: Vector a
        vec2 = valloc (len + 1)
        vec3 = generate_loop vec2 1 (len+1) (\i -> nth vec (i-1))
        vec4 = inplacevupdate vec3 0 x
    in vec4

lcons :: a -> Vector a %1-> Vector a
{-# INLINE lcons #-}
lcons x vec = unsafeToLinear (\y -> cons x y) vec

----------------------------------
-- TODO: review things after this.

filter_loop :: Vector Int -> Int -> Int -> Int -> Vector a -> Vector a -> Vector a
filter_loop idxs write_at start end from to =
    if start == end
    then to
    else
        let idx = nth idxs start
        in if idx == (-1)
           then filter_loop idxs write_at (start+1) end from to
           else
               let elt = nth from idx
                   to1 = inplacevupdate to write_at elt
               in filter_loop idxs (write_at+1) (start+1) end from to1

filter :: (a -> Bool) -> Vector a -> Vector a
{-# INLINE filter #-}
filter f vec =
    let idxs :: Vector Int
        idxs = generate (vlength vec) (\i -> if f (nth vec i) then i else (-1))
        num_ones = foldl (\(acc :: Int) (x :: Int) -> if x == (-1) then acc else acc + 1) 0 idxs
        to :: Vector a
        to = valloc num_ones
        len_idxs = vlength idxs
    in filter_loop idxs 0 0 len_idxs vec to
