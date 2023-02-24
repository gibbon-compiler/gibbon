{-# LANGUAGE NoImplicitPrelude #-}

module Mergesort where

import Gibbon.Prelude
import Gibbon.Vector
import Gibbon.Vector.Parallel

-- import QuickSort

--------------------------------------------------------------------------------

goto_seqmerge :: Int
{-# INLINE goto_seqmerge #-}
goto_seqmerge = 4096

gotoQuickSort :: Int
{-# INLINE gotoQuickSort #-}
gotoQuickSort = 8192

--------------------------------------------------------------------------------

mergesort_debugPrint :: Vector Int -> ()
mergesort_debugPrint vec =
    let _ = printVec (\i -> printint i) vec
        _ = print_newline ()
    in ()

binarySearch' :: Int -> Int -> (a -> a -> Int) -> Vector a -> a -> Int
binarySearch' lo hi cmp vec query =
    let n = hi - lo
    in if n == 0
       then lo
       else let mid = lo + (div n 2)
                pivot = nth vec mid
                -- IMPORTANT:
                tst = cmp query pivot
            in if tst < 0
               then binarySearch' lo mid cmp vec query
               else if tst > 0
                    then binarySearch' (mid+1) hi cmp vec query
                    else mid

-- | Return 'query's *position* in 'vec'.
--
-- That is, return a *p* s.t.
-- (1) elements vec[0]..vec[p] are less than query, and
-- (2) elements vec[p+1]..vec[end] are greater than query.
binarySearch :: (a -> a -> Int) -> Vector a -> a -> Int
{-# INLINE binarySearch #-}
binarySearch cmp vec query = binarySearch' 0 (length vec) cmp vec query

--------------------------------------------------------------------------------

-- | Copy elements from 'from' to 'to'.
--
-- from[from_idx]    ===>   to[to_idx]
-- from[from_idx+1]  ===>   to[to_idx+1]
-- ...
write_loop_seq :: Int -> Int -> Int -> Vector a -> Vector a -> Vector a
write_loop_seq to_idx from_idx end from to =
    if from_idx == end
    then to
    else let to1 = inplaceUpdate to_idx (nth from from_idx) to
         in write_loop_seq (to_idx+1) (from_idx+1) end from to1

-- | The main sequential merge function.
-- i1 index into src_1
-- i2 index into src_2
-- j index into tmp (output).
writeMerge_seq_loop :: Int -> Int -> Int -> Int -> Int -> (a -> a -> Int) -> Vector a -> Vector a -> Vector a -> Vector a
writeMerge_seq_loop i1 i2 j n1 n2 cmp src_1 src_2 tmp =
    -- copy src_2 to tmp.
    if i1 == n1
    then let -- tmp_1 = slice i2 (n2-i2) src_2
             tmp_2 = write_loop_seq j i2 n2 src_2 tmp
         in tmp_2
    -- copy src_1 to tmp.
    else if i2 == n2
         then let -- tmp_1 = slice i1 (n1-i1) src_1
                  tmp_2 = write_loop_seq j i1 n1 src_1 tmp
              in tmp_2
    -- compare elements from both arrays and write the smaller one at j.
         else let x1 = nth src_1 i1
                  x2 = nth src_2 i2
              in if cmp x1 x2 < 0
                 then let tmp_1 = inplaceUpdate j x1 tmp
                      in writeMerge_seq_loop (i1+1) i2 (j+1) n1 n2 cmp src_1 src_2 tmp_1
                 else let tmp_1 = inplaceUpdate j x2 tmp
                      in writeMerge_seq_loop i1 (i2+1) (j+1) n1 n2 cmp src_1 src_2 tmp_1


-- | Merge 'src_1' and 'src_2' into 'tmp'.
writeMerge_seq :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a -> Vector a
{-# INLINE writeMerge_seq #-}
writeMerge_seq cmp src_1 src_2 tmp =
    let n1 = length src_1
        n2 = length src_2
        res = writeMerge_seq_loop 0 0 0 n1 n2 cmp src_1 src_2 tmp
    in res

--------------------------------------------------------------------------------

-- | Sequential variant of 'writeSort1'.
writeSort1_seq :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a
writeSort1_seq cmp src tmp =
    let len = length src in
    if len < gotoQuickSort
    -- then quickSort_par' 0 (length s) f s
    then inplaceSort cmp src
    else
        let half = div len 2
            (src_l,src_r) = splitAt half src
            (tmp_l,tmp_r) = splitAt half tmp
            tmp_l1 = writeSort2_seq cmp src_l tmp_l
            tmp_r1 = writeSort2_seq cmp src_r tmp_r
            res = writeMerge_seq cmp tmp_l1 tmp_r1 src
        in res

-- | Sequential variant of 'writeSort2'.
writeSort2_seq :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a
writeSort2_seq cmp src tmp =
    let len = length src in
    if len < gotoQuickSort
    then
        let tmp_1 = write_loop_seq 0 0 len src tmp
        -- in quickSort_par' 0 (length t1) f t1
        in inplaceSort cmp tmp_1
    else
        let half = div len 2
            (src_l,src_r) = splitAt half src
            (tmp_l,tmp_r) = splitAt half tmp
            src_l1 = writeSort1_seq cmp src_l tmp_l
            src_r1 = writeSort1_seq cmp src_r tmp_r
            res = writeMerge_seq cmp src_l1 src_r1 tmp
        in res

-- | Sequential in-place merge sort.
mergeSort'_seq :: (a -> a -> Int) -> Vector a -> Vector a
{-# INLINE mergeSort'_seq #-}
mergeSort'_seq cmp src =
    let tmp :: Vector a
        tmp = alloc (length src)
        tmp2 = writeSort1_seq cmp src tmp
    in src

-- | Sequential merge sort, copies the input into a separate array and then sorts
--   that array in-place.
mergeSort_seq :: (a -> a -> Int) -> Vector a -> Vector a
{-# INLINE mergeSort_seq #-}
mergeSort_seq cmp vec =
    let vec2 = copy vec
        vec3 = mergeSort'_seq cmp vec2
    in vec3

--------------------------------------------------------------------------------

check_sorted :: (a -> a -> Int) -> Vector a -> ()
check_sorted cmp sorted =
  let len = length sorted in
  if len <= 1
  then print_check True
  else let arr1 = slice 0 (len - 2) sorted
           check = ifoldl (\acc i elt1 -> let elt2 = nth arr1 (i+1)
                                          in acc && (cmp elt1 elt2 <= 0))
                   True
                   arr1
       in print_check check

test_main :: ()
test_main =
    let n = sizeParam
        arr = generate n (\i -> (n-i))
        sorted = mergeSort_seq compare_int arr
        chk = ifoldl (\acc i n -> acc && ((i+1) == n)) True sorted
        -- _ = printVec (\i -> printint i) sorted
        -- _ = print_newline()
    in print_check chk

bench_main :: ()
bench_main =
            let n = sizeParam
                arr = generate n (\i -> intToFloat (rand))
                sorted = iterate (mergeSort_seq compare_float arr)
            in check_sorted compare_float sorted

gibbon_main = bench_main
