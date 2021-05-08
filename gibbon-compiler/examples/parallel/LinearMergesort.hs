{-# LANGUAGE LinearTypes #-}

module LinearMergesort where

import Gibbon.Prelude
import Gibbon.Vector
import Gibbon.Vector.Parallel


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

binarySearch' :: Int -> Int -> (a -> a -> Int) -> Vector a %1-> a -> Int
binarySearch' lo hi cmp vec query =
    let n = hi - lo in
    if n == 0
    then lseq vec lo
    else
        nth2 vec (lo+(div n 2)) &
          \(Ur pivot, vec1) ->
              if (cmp query pivot) < 0
              then binarySearch' lo (lo+(div n 2)) cmp vec1 query
              else if (cmp query pivot) > 0
                   then binarySearch' ((lo+(div n 2))+1) hi cmp vec1 query
                   else lseq vec1 (lo+(div n 2))

binarySearch_go :: (a -> a -> Int) -> Vector a -> a -> Ur Int
{-# INLINE binarySearch_go #-}
binarySearch_go cmp vec query = Ur (binarySearch' 0 (length vec) cmp vec query)

binarySearch :: (a -> a -> Int) -> Vector a %1-> a -> Ur Int
binarySearch cmp vec query = unsafeToLinear (\vec2 -> binarySearch_go cmp vec2 query) vec

--------------------------------------------------------------------------------

write_loop_seq :: Int -> Int -> Int -> Vector a %1-> Vector a %1-> Vector a
write_loop_seq to_idx from_idx end from to =
    if from_idx == end
    then lseq from to
    else
        nth2 from from_idx &
            \(Ur val, from1) ->
                inplaceUpdate to_idx val to &
                    \to1 -> write_loop_seq (to_idx+1) (from_idx+1) end from1 to1


write_loop :: Int -> Int -> Int -> Vector a %1-> Vector a %1-> Vector a
write_loop to_idx from_idx end from to =
    if (end - from_idx) < goto_seqmerge
    then write_loop_seq to_idx from_idx end from to
    else let mid = div (from_idx + end) 2
         in unsafeAlias from &
                \(from1,from2) ->
                    unsafeAlias to &
                        \(to1,to2) ->
                            spawn (write_loop to_idx from_idx mid from1 to1) &
                                \to4 ->
                                    write_loop (to_idx+mid-from_idx) mid end from2 to2 &
                                        \to5 ->
                                            lsync &
                                                \(Ur _) ->
                                                    lseq to4 to5

writeMerge_seq_loop :: Int -> Int -> Int -> Int -> Int -> (a -> a -> Int) -> Vector a %1-> Vector a %1-> Vector a %1-> Vector a
writeMerge_seq_loop i1 i2 j n1 n2 cmp src_1 src_2 tmp =
    if (i1 == n1)
    then lseq src_1 (write_loop_seq j i2 n2 src_2 tmp)
    else if i2 == n2
         then lseq src_2 (write_loop_seq j i1 n1 src_1 tmp)
         else
              nth2 src_1 i1 &
                 \(Ur x1, src_11) ->
                     nth2 src_2 i2 &
                         \(Ur x2, src_21) ->
                             if cmp x1 x2 < 0
                             then
                                 inplaceUpdate j x1 tmp &
                                     \tmp_1 -> writeMerge_seq_loop (i1+1) i2 (j+1) n1 n2 cmp src_11 src_21 tmp_1
                             else
                                 inplaceUpdate j x2 tmp &
                                     \tmp_1 -> writeMerge_seq_loop i1 (i2+1) (j+1) n1 n2 cmp src_11 src_21 tmp_1

writeMerge_seq :: (a -> a -> Int) -> Int -> Vector a %1-> Int -> Vector a %1-> Vector a %1-> Vector a
writeMerge_seq cmp n1 src_1 n2 src_2 tmp = writeMerge_seq_loop 0 0 0 n1 n2 cmp src_1 src_2 tmp

writeMerge_par :: (a -> a -> Int) -> Int -> Vector a %1-> Int -> Vector a %1-> Vector a %1-> Vector a
writeMerge_par cmp n1 src_10 n2 src_20 tmp0 =
    if ((n1+n2) <= goto_seqmerge || n1 == 0 || n2 == 0)
    then writeMerge_seq cmp n1 src_10 n2 src_20 tmp0
    else
        if (n1 == 0)
        then lseq src_10 (write_loop 0 0 n2 src_20 tmp0)
        else if (n2 == 0)
             then lseq src_20 (write_loop 0 0 n1 src_10 tmp0)
             else writeMerge_par_go cmp (div n1 2) src_10 src_20 tmp0

writeMerge_par_go :: (a -> a -> Int) -> Int -> Vector a %1-> Vector a %1-> Vector a %1-> Vector a
writeMerge_par_go cmp mid1 src_1 src_2 tmp =
    nth2 src_1 mid1 &
        \(Ur pivot, src_11) ->
            unsafeAlias src_2 &
                \(src_20,src_21) ->
                    binarySearch cmp src_20 pivot &
                        \(Ur mid2) ->
                            writeMerge_par_go2 cmp mid1 mid2 pivot src_11 src_21 tmp


writeMerge_par_go2 :: (a -> a -> Int) -> Int -> Int -> a -> Vector a %1-> Vector a %1-> Vector a %1-> Vector a
writeMerge_par_go2 cmp mid1 mid2 pivot src_1 src_2 tmp00 =
    lsplitAt mid1 src_1 &
        \(Ur n5,src_1_l,Ur _,src_1_r0) ->
            lsplitAt 1 src_1_r0 &
                \(Ur _one1, src_one,Ur n6, src_1_r) ->
                    lsplitAt mid2 src_2 &
                        \(Ur n3,src_2_l,Ur n4,src_2_r) ->
                            lsplitAt (mid1+mid2) tmp00 &
                                \(Ur _,tmp_l,Ur _,tmp_r0) ->
                                    lsplitAt 1 tmp_r0 &
                                        \(Ur _one2,tmp_one,Ur _,tmp_r) ->
                                            write_loop_seq 0 0 1 src_one tmp_one &
                                                \tmp_one' ->
                                                    spawn (writeMerge_par cmp n5 src_1_l n3 src_2_l tmp_l) &
                                                        \tmp_l1 ->
                                                            writeMerge_par cmp n6 src_1_r n4 src_2_r tmp_r &
                                                                \tmp_r1 ->
                                                                    lsync &
                                                                        \(Ur _) ->
                                                                            merge (merge tmp_l1 tmp_one') tmp_r1

writeSort1_par :: (a -> a -> Int) -> Vector a %1-> Vector a %1-> Vector a
writeSort1_par cmp src00 tmp =
    length2 src00 &
        \(Ur len, src0) ->
            if len <= 1
            then lseq tmp src0
            else unsafeAlias src0 &
                   \(src, src1) ->
                       lsplitAt (div len 2) src &
                           \(Ur _n1,src_l,Ur _n2,src_r) ->
                               lsplitAt (div len 2) tmp &
                                   \(Ur n3,tmp_l,Ur n4,tmp_r) ->
                                       spawn (writeSort2_par cmp src_l tmp_l) &
                                           \tmp_l1 ->
                                               writeSort2_par cmp src_r tmp_r &
                                                   \tmp_r1 ->
                                                       lsync &
                                                           \(Ur _) ->
                                                               writeMerge_par cmp n3 tmp_l1 n4 tmp_r1 src1


writeSort1_seq :: (a -> a -> Int) -> Vector a %1-> Vector a %1-> Vector a
writeSort1_seq cmp src00 tmp =
    length2 src00 &
        \(Ur len, src0) ->
            if len <= 1
            then lseq tmp src0
            else unsafeAlias src0 &
                   \(src, src1) ->
                       lsplitAt (div len 2) src &
                           \(Ur _n1,src_l,Ur _n2,src_r) ->
                               lsplitAt (div len 2) tmp &
                                   \(Ur n3,tmp_l,Ur n4,tmp_r) ->
                                       writeSort2_seq cmp src_l tmp_l &
                                           \tmp_l1 ->
                                               writeSort2_seq cmp src_r tmp_r &
                                                   \tmp_r1 ->
                                                       writeMerge_seq cmp n3 tmp_l1 n4 tmp_r1 src1

writeSort2_par :: (a -> a -> Int) -> Vector a %1-> Vector a %1-> Vector a
writeSort2_par cmp src0 tmp0 =
    length2 src0 &
        \(Ur len, src) ->
            if len <= 1
            then write_loop_seq 0 0 1 src tmp0
            else unsafeAlias tmp0 &
                     \(tmp, tmp1) ->
                         lsplitAt (div len  2) src &
                             \(Ur n1,src_l,Ur n2,src_r) ->
                                 lsplitAt (div len 2) tmp &
                                     \(Ur _n3,tmp_l,Ur _n4,tmp_r) ->
                                         spawn (writeSort1_par cmp src_l tmp_l) &
                                             \src_l1 ->
                                                 writeSort1_par cmp src_r tmp_r &
                                                     \src_r1 ->
                                                         lsync &
                                                             \(Ur _) ->
                                                                 writeMerge_par cmp n1 src_l1 n2 src_r1 tmp1

writeSort2_seq :: (a -> a -> Int) -> Vector a %1-> Vector a %1-> Vector a
writeSort2_seq cmp src0 tmp0 =
    length2 src0 &
        \(Ur len, src) ->
            if len <= 1
            then write_loop_seq 0 0 1 src tmp0
            else unsafeAlias tmp0 &
                     \(tmp, tmp1) ->
                         lsplitAt (div len  2) src &
                             \(Ur n1,src_l,Ur n2,src_r) ->
                                 lsplitAt (div len 2) tmp &
                                     \(Ur _n3,tmp_l,Ur _n4,tmp_r) ->
                                         writeSort1_seq cmp src_l tmp_l &
                                             \src_l1 ->
                                                 writeSort1_seq cmp src_r tmp_r &
                                                     \src_r1 ->
                                                         writeMerge_seq cmp n1 src_l1 n2 src_r1 tmp1

mergeSort'_seq :: (a -> a -> Int) -> Vector a %1-> Vector a
{-# INLINE mergeSort'_seq #-}
mergeSort'_seq cmp src =
    length2 src &
        \(Ur len, src1) ->
            unsafeAlias src1 &
                \(src2,src3) ->
                    writeSort1_seq cmp src2 (alloc len) &
                        \tmp2 ->
                            lseq tmp2 src3

mergeSort_seq :: (a -> a -> Int) -> Vector a %1-> Vector a
{-# INLINE mergeSort_seq #-}
mergeSort_seq cmp vec = mergeSort'_seq cmp (lcopy vec)

mergeSort'_par :: (a -> a -> Int) -> Vector a %1-> Vector a
{-# INLINE mergeSort'_par #-}
mergeSort'_par cmp src =
    length2 src &
        \(Ur len, src1) ->
            unsafeAlias src1 &
                \(src2,src3) ->
                    writeSort1_par cmp src2 (alloc len) &
                        \tmp2 ->
                            lseq tmp2 src3

mergeSort_par :: (a -> a -> Int) -> Vector a %1-> Vector a
{-# INLINE mergeSort_par #-}
mergeSort_par cmp vec = mergeSort'_par cmp (lcopy vec)

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
        sorted = mergeSort_par compare_int arr
        chk = ifoldl (\acc i n -> acc && ((i+1) == n)) True sorted
        -- _ = printVec (\i -> printint i) sorted
        -- _ = print_newline()
    in print_check chk

gibbon_main =
        let s = benchProgParam in
        if eqsym s (quote "seqmergesort")
        then
            let n = sizeParam
                arr = generate n (\i -> intToFloat (rand))
                sorted = iterate (mergeSort_seq compare_float arr)
            in check_sorted compare_float sorted
        else
            let n = sizeParam
                arr = generate n (\i -> intToFloat (rand))
                sorted = iterate (mergeSort_par compare_float arr)
            in check_sorted compare_float sorted
