-- | An implementation of the two-pivot QuickSort algorithm (copied from MPL's examples)
module QuickSort where

import Gibbon.Vector
import Gibbon.Vector.Parallel
import InsertionSort

--------------------------------------------------------------------------------

-- newline :: ()
-- newline = printsym (quote "\n")

rotate :: Int -> Int -> Int -> Vector a -> Vector a
rotate i j k vec =
    let elt_i = nth vec i
        elt_j = nth vec j
        elt_k = nth vec k
        vec2 = inplacevupdate vec i elt_k
        vec3 = inplacevupdate vec j elt_i
        vec4 = inplacevupdate vec k elt_j
    in vec4

toFront :: Int -> Int -> Int -> Int -> Vector a -> Vector a
toFront i size m a vec =
    if i < size
    then let vec2 = swap (a + i) (a + m*(i+1)) vec
         in toFront (i+1) size m a vec2
    else vec

sortToFront :: Int -> Int -> Int -> (a -> a -> Int) -> Vector a -> Vector a
sortToFront size a n f vec =
    let m = div n (size+1)
        vec2 = toFront 0 size m a vec
        vec3 = insertionSort'' f a size vec2
    in vec3

cmp :: Int -> Int -> (a -> a -> Int) -> Vector a -> Int
cmp i j f vec =
    let a = nth vec i
        b = nth vec j
    in f a b

twoPivots :: (a -> a -> Int) -> Int -> Int -> Vector a -> Vector a
twoPivots f a n vec =
    -- if n < 80
    -- then -- (cmp a (a+n-1) f vec) = GREATER
         if (cmp a (a+n-1) f vec) > 0
         then let vec2 = swap a (a+n-1) vec
              in vec2
         else vec
    -- else let vec2 = sortToFront 10 a n f vec
    --          -- _ = printVec (\i -> printint i) vec2
    --          -- _ = newline
    --          vec3 = swap (a+1) a vec2
    --          vec4 = swap (a+3) (a+n-1) vec3
    --      in vec4

right :: Int -> Int -> (a -> a -> Int) -> Vector a -> Int
right r p2 f vec =
    -- (cmp r p2 f vec) = GREATER
    if (cmp r p2 f vec) > 0
    then right (r-1) p2 f vec
    else r

split3_loop :: Int -> Int -> Int -> Int -> Int -> (a -> a -> Int) -> Vector a -> (Int, Int)
split3_loop l m r p1 p2 f vec =
    if m > r then (l,m)
    else -- cmp m p1 f vec = LESS
         if cmp m p1 f vec < 0
         then let vec2 = swap m l vec
              in split3_loop (l+1) (m+1) r p1 p2 f vec2
         else -- cmp m p2 f vec = GREATER
              if cmp m p2 f vec > 0
              then -- (cmp r p1 f vec) = LESS
                   if (cmp r p1 f vec) < 0
                   then let vec2 = rotate l m r vec
                            r2 = right (r-1) p2 f vec
                        in split3_loop (l+1) (m+1) r2 p1 p2 f vec2
                   else let vec2 = swap m r vec
                            r2 = right (r-1) p2 f vec
                        in split3_loop l (m+1) r2 p1 p2 f vec2
              else split3_loop l (m+1) r p1 p2 f vec


-- Splits based on two pivots (p1 and p2) into 3 parts:
-- less than p1, greater than p2, and the rest in the middle.
-- The pivots themselves end up at the two ends.
-- If the pivots are the same, returns a false flag to indicate middle
-- need not be sorted.
split3 :: Int -> Int -> (a -> a -> Int) -> Vector a -> (Int, Int, Bool)
split3 a n f vec =
    let vec2 = twoPivots f a n vec
        p1 = a
        p2 = a+n-1
        r2 = right (a+n-2) p2 f vec2
        (l,m) = split3_loop (a+1) (a+1) r2 p1 p2 f vec2
    in (l, m, (cmp p1 p2 f vec) < 0)

-- Sort in place.
quickSort_seq' :: Int -> Int -> (a -> a -> Int) -> Vector a -> Vector a
quickSort_seq' a n f vec =
    if n < 16 then insertionSort' f vec else
    let (l,m,doMid) = split3 a n f vec
        vec2 =  quickSort_seq' a (l - a) f vec
    in if doMid
       then let vec3 = quickSort_seq' l (m-l) f vec2
                vec4 = quickSort_seq' m (a+n-m) f vec3
            in vec4
       else let vec4 = quickSort_seq' m (a+n-m) f vec2
            in vec4

-- | Returns a new sorted vector.
quickSort_seq :: (a -> a -> Int) -> Vector a -> Vector a
quickSort_seq f vec =
    let vec2 = copy_par vec
    in quickSort_seq' 0 (length vec2) f vec2

-- Sort in place.
quickSort_par' :: Int -> Int -> (a -> a -> Int) -> Vector a -> Vector a
quickSort_par' a n f vec =
    if n < 16 then insertionSort' f vec
    else if n < 32
    then quickSort_seq' a n f vec
    else let (l,m,doMid) = split3 a n f vec
             vec2 = spawn (quickSort_par' a (l - a) f vec)
         in if doMid
            then let vec3 = spawn (quickSort_par' l (m-l) f vec)
                     vec4 = quickSort_par' m (a+n-m) f vec
                     _ = sync
                 in vec4
            else let vec4 = quickSort_par' m (a+n-m) f vec
                     _ = sync
                 in vec4

-- | Returns a new sorted vector.
quickSort_par :: (a -> a -> Int) -> Vector a -> Vector a
quickSort_par f vec =
    let vec2 = copy_par vec
    in quickSort_par' 0 (length vec2) f vec2


cmp1 :: Int -> Int -> Int
cmp1 c d = d - c

gibbon_main =
    let n = sizeParam
        vec = generate n (\i -> n - i)
        vec2 = timeit (quickSort_seq (\a b -> b - a) vec)
        vec3 = timeit (vsort vec cmp1)
        -- vec2 = quickSort_par (\a b -> b - a) vec
        -- _ = printVec (\i -> printint i) vec
        -- _ = newline
        -- _ = printVec (\i -> printint i) vec2
        -- _ = newline
        test1 = length vec == length vec2
        test2 = ifoldl (\acc i elt -> acc && elt == (i+1)) True vec2
    in test1 && test2
