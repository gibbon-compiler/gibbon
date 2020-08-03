module MergeSort where

import Gibbon.Vector
import Gibbon.Vector.Parallel

-- import QuickSort

--------------------------------------------------------------------------------

newline :: ()
newline = printsym (quote "\n")

debugPrint :: Vector Int -> ()
debugPrint vec =
    let _ = printVec (\i -> printint i) vec
        _ = newline
    in ()

binarySearch' :: Int -> Int -> (a -> a -> Int) -> Vector a -> a -> Int
binarySearch' lo hi f s x =
    let n = hi - lo
    in if n == 0
       then lo
       else let mid = lo + (div n 2)
                pivot = nth s mid
                cmp = f pivot x
            in if cmp < 0
               then binarySearch' lo mid f s x
               else if cmp > 0
                    then binarySearch' (mid+1) hi f s x
                    else mid

binarySearch :: (a -> a -> Int) -> Vector a -> a -> Int
binarySearch f s x = binarySearch' 0 (length s) f s x

write_loop_seq :: Int -> Int -> Int -> Vector a -> Vector a -> Vector a
write_loop_seq idx offset end from to =
    if idx == end
    then to
    else let to1 = inplacevupdate to (idx+offset) (nth from idx)
         in write_loop_seq (idx+1) offset end from to1

write_loop :: Int -> Int -> Int -> Vector a -> Vector a -> Vector a
write_loop idx offset end from to =
    if (end - idx) < 4096
    then write_loop_seq idx offset end from to
    else let mid = div (idx + end) 2
             to1 = spawn (write_loop idx offset mid from to)
             to2 = write_loop mid offset end from to
             _ = sync
         in to2

-- i1 index into s1
-- i2 index into s2
-- j index into output
writeMerge_seq_loop :: Int -> Int -> Int -> Int -> Int -> (a -> a -> Int) -> Vector a -> Vector a -> Vector a -> Vector a
writeMerge_seq_loop i1 i2 j n1 n2 f s1 s2 t =
    if i1 == n1
    then let tmp1 = vslice i2 (n2-i2) s2
             t2 = write_loop 0 j (n2-i2) tmp1 t
         in t2
    else if i2 == n2
         then let tmp1 = vslice i1 (n1-i1) s1
                  t1 = write_loop 0 j (n1-i1) tmp1 t
              in t1
         else let x1 = nth s1 i1
                  x2 = nth s2 i2
              in if f x1 x2 > 0
                 then let t1 = inplacevupdate t j x1
                      in writeMerge_seq_loop (i1+1) i2 (j+1) n1 n2 f s1 s2 t1
                 else let t1 = inplacevupdate t j x2
                      in writeMerge_seq_loop i1 (i2+1) (j+1) n1 n2 f s1 s2 t1


writeMerge_seq :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a -> Vector a
writeMerge_seq f s1 s2 t =
    let n1 = length s1
        n2 = length s2
        res = writeMerge_seq_loop 0 0 0 n1 n2 f s1 s2 t
    in res


writeMerge :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a -> Vector a
writeMerge f s1 s2 t =
    if length t < 4096
    then writeMerge_seq f s1 s2 t
    else
        let n1 = length s1
            n2 = length s2
        in if n1 == 0
           then write_loop 0 0 n2 s2 t
           else let mid1 = div n1 2
                    pivot = nth s1 mid1
                    mid2 = binarySearch f s2 pivot
                    l1 = vslice 0 mid1 s1
                    r1 = vslice (mid1+1) (n1 - (mid1+1)) s1
                    l2 = vslice 0 mid2 s2
                    r2 = vslice mid2 (n2-mid2) s2
                    _ = inplacevupdate t (mid1+mid2) pivot
                    len_t = length t
                    tl = vslice 0 (mid1+mid2) t
                    tr = vslice (mid1+mid2+1) (len_t - (mid1+mid2+1)) t
                    tl1 = spawn (writeMerge f l1 l2 tl)
                    tr1 = writeMerge f r1 r2 tr
                    _ = sync
                in t

--------------------------------------------------------------------------------

gotoQuickSort :: Int
gotoQuickSort = 1024

writeSort1 :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a
writeSort1 f s t =
    let len = length s in
    if len < gotoQuickSort
    -- then inplacevsort s f
    then inplacevsort s f
    else
        let half = div len 2
            (sl,sr) = splitAt half s
            (tl,tr) = splitAt half t
            tl1 = spawn (writeSort2 f sl tl)
            tr1 = writeSort2 f sr tr
            _ = sync
            res = writeMerge f tl1 tr1 s
        in res

writeSort2 :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a
writeSort2 f s t =
    let len =length s in
    if len < gotoQuickSort
    then
        let t1 = write_loop 0 0 len s t
        in inplacevsort t1 f
    else
        let half = div len 2
            (sl,sr) = splitAt half s
            (tl,tr) = splitAt half t
            sl1 = spawn (writeSort1 f sl tl)
            sr1 = (writeSort1 f sr tr)
            _ = sync
            res = writeMerge f sl1 sr1 t
        in res

mergeSort' :: (a -> a -> Int) -> Vector a -> Vector a
mergeSort' f s =
    let t :: Vector a
        t = valloc (length s)
        t2 = writeSort1 f s t
    in s

mergeSort :: (a -> a -> Int) -> Vector a -> Vector a
mergeSort f vec =
    let vec2 = copy_par vec
        vec3 = mergeSort' f vec2
    in vec3

cmp4 :: Int -> Int -> Int
cmp4 a b = b - a

gibbon_main =
    let n = sizeParam
        vec = generate n (\i -> n - i)
        vec2 = timeit (mergeSort (\a b -> b - a) vec)
        vec3 = timeit (inplacevsort vec cmp4)
        -- _ = printVec (\i -> printint i) vec
        -- _ = newline
        -- _ = printVec (\i -> printint i) vec2
        -- _ = newline
        test1 = length vec == length vec2
        test2 = ifoldl (\acc i elt -> acc && elt == (i+1)) True vec2
        test3 = ifoldl (\acc i elt -> acc && elt == (i+1)) True vec3
    in (test1 && test2, test3)
