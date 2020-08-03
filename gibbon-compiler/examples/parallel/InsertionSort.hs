module InsertionSort where

import Gibbon.Vector

swap :: Int -> Int -> Vector a -> Vector a
swap i j vec =
    let elt_i = nth vec i
        elt_j = nth vec j
        vec2 = inplacevupdate vec i elt_j
        vec3 = inplacevupdate vec j elt_i
    in vec3

inner :: (a -> a -> Int) -> Int -> Int -> Int -> Int -> Vector a -> Vector a
inner cmp start limit i j vec =
    if j == start
    then outer cmp start limit (i+1) vec
    else
        let j' = j-1
            elt_j = nth vec j
            elt_j' = nth vec j' in
        if (cmp elt_j elt_j') >= 1
        then let vec2 = swap j j' vec
             in inner cmp start limit i (j-1) vec2
        else
            outer cmp start limit (i+1) vec

outer :: (a -> a -> Int) -> Int -> Int -> Int -> Vector a -> Vector a
outer cmp start limit i vec =
    if i >= limit
    then vec
    else inner cmp start limit i i vec

insertionSort'' :: (a -> a -> Int) -> Int -> Int -> Vector a -> Vector a
insertionSort'' cmp start n vec = outer cmp start (start+n) (start+1) vec

-- | Sort in place.
insertionSort' :: (a -> a -> Int) -> Vector a -> Vector a
insertionSort' cmp vec =
    let len  = length vec
        vec2 = insertionSort'' cmp 0 len vec
    in vec2

-- | Returns a new sorted vector.
insertionSort :: (a -> a -> Int) -> Vector a -> Vector a
insertionSort cmp vec =
    let vec2 = copy vec
        vec3 = insertionSort' cmp vec2
    in vec3

gibbon_main =
    let vec = generate 10 (\i -> 10 - i)
        vec2 = insertionSort (\a b -> b - a) vec
        -- _ = printVec (\i -> printint i) vec
        -- _ = printsym (quote "\n")
        -- _ = printVec (\i -> printint i) vec2
        -- _ = printsym (quote "\n")
        test1 = length vec == length vec2
        test2 = ifoldl (\acc i elt -> acc && elt == (i+1)) True vec2
    in test1 && test2
