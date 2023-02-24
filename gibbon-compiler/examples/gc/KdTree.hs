{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude   #-}

module KdTree where

import Gibbon.Prelude
import Gibbon.Vector

import Geometry

--------------------------------------------------------------------------------
-- The main algorithm

type Point3d = (Float, Float, Float)

data KdTree = KdLeaf Float  -- ^ x coord
                     Float  -- ^ y coord
                     Float  -- ^ z coord

            | KdNode Float  -- x coord
                     Float  -- y coord
                     Float  -- z coood
                     Int    -- ^ number of elements in this node
                     Int    -- ^ splitting axis (0 == x, 1 == y)
                     Float  -- ^ split value
                     Float  -- ^ min_x
                     Float  -- ^ max_x
                     Float  -- ^ min_y
                     Float  -- ^ max_y
                     Float  -- ^ min_z
                     Float  -- ^ max_z
                     KdTree -- ^ left
                     KdTree -- ^ right

           | KdEmpty

copy_kdtree :: KdTree -> KdTree
copy_kdtree tr =
  case tr of
    KdEmpty -> KdEmpty
    KdLeaf x y z -> KdLeaf x y z
    KdNode x y z a b c d e f g h i left right ->
      KdNode x y z a b c d e f g h i (copy_kdtree left) (copy_kdtree right)

print_kdtree :: KdTree -> ()
print_kdtree tr =
  case tr of
    KdEmpty ->
        let _ = printsym (quote "empty{}")
        in ()
    KdLeaf x y z ->
      let _ = printsym (quote "leaf{")
          _ = print_point3d (x,y,z)
          _ = printsym (quote "}")
      in ()
    KdNode x y z _ axis _ _ _ _ _ _ _ left right ->
      let _ = printsym (quote "node{ point: ")
          _ = print_point3d (x,y,z)
          _ = printsym (quote ", axis: ")
          _ = printint axis
          _ = printsym (quote ", left: ")
          _ = print_kdtree left
          _ = printsym (quote ", right: ")
          _ = print_kdtree right
          _ = printsym (quote "}")
      in ()

get_minx_kdtree :: KdTree -> Float
get_minx_kdtree tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ min_x _ _ _ _ _ _ _ -> min_x
    KdLeaf x _ _                     -> x

get_maxx_kdtree :: KdTree -> Float
get_maxx_kdtree tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ max_x _ _ _ _ _ _ -> max_x
    KdLeaf x _ _                     -> x

get_miny_kdtree :: KdTree -> Float
get_miny_kdtree tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ min_y _ _ _ _ _ -> min_y
    KdLeaf _ y _                     -> y

get_maxy_kdtree :: KdTree -> Float
get_maxy_kdtree tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ _ max_y _ _ _ _ -> max_y
    KdLeaf _ y _                     -> y

get_minz_kdtree :: KdTree -> Float
get_minz_kdtree tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ _ _ min_z _ _ _ -> min_z
    KdLeaf _ _ z                     -> z

get_maxz_kdtree :: KdTree -> Float
get_maxz_kdtree tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ _ _ _ max_z _ _ -> max_z
    KdLeaf _ _ z                     -> z


get_total_points_kdtree :: KdTree -> Int
get_total_points_kdtree tr =
  case tr of
    KdEmpty -> 0
    KdNode _ _ _ elems _ _ _ _ _ _ _ _ _ _ -> elems
    KdLeaf _ y _                     -> 1

getx_kdtree :: KdTree -> Float
getx_kdtree tr =
    case tr of
        KdEmpty -> 0.0
        KdNode x _ _ _ _ _ _ _ _ _ _ _ _ _ -> x
        KdLeaf x _ _                       -> x

gety_kdtree :: KdTree -> Float
gety_kdtree tr =
    case tr of
        KdEmpty -> 0.0
        KdNode _ y _ _ _ _ _ _ _ _ _ _ _ _ -> y
        KdLeaf _ y _                       -> y

getz_kdtree :: KdTree -> Float
getz_kdtree tr =
    case tr of
        KdEmpty -> 0.0
        KdNode _ _ z _ _ _ _ _ _ _ _ _ _ _ -> z
        KdLeaf _ _ z                       -> z

mkKdTreeWithAxis_seq :: Int -> Vector Point3d -> KdTree
mkKdTreeWithAxis_seq axis pts =
    let len = vlength pts in
    if len == 0
    then KdEmpty
    else if len == 1
    then let (x,y,z) = nth pts 0
         in KdLeaf x y z
    else let sorted_pts = sort_point3d axis pts
             pivot_idx  = div len 2
             pivot      = nth sorted_pts pivot_idx
             (x,y,z)    = pivot
             left_pts   = slice 0 pivot_idx sorted_pts
             right_pts  = slice (pivot_idx+1) (len - pivot_idx - 1) sorted_pts
             next_axis  = getNextAxis_3d axis
             left_tr    = mkKdTreeWithAxis_seq next_axis left_pts
             right_tr   = mkKdTreeWithAxis_seq next_axis right_pts
             min_x      = minFloat x (minFloat (get_minx_kdtree left_tr) (get_minx_kdtree right_tr))
             max_x      = maxFloat x (maxFloat (get_maxx_kdtree left_tr) (get_maxx_kdtree right_tr))
             min_y      = minFloat y (minFloat (get_miny_kdtree left_tr) (get_miny_kdtree right_tr))
             max_y      = maxFloat y (maxFloat (get_maxy_kdtree left_tr) (get_maxy_kdtree right_tr))
             min_z      = minFloat z (minFloat (get_minz_kdtree left_tr) (get_minz_kdtree right_tr))
             max_z      = maxFloat z (maxFloat (get_maxz_kdtree left_tr) (get_maxz_kdtree right_tr))
             total_points= (get_total_points_kdtree left_tr) + (get_total_points_kdtree right_tr) + 1
         in KdNode x y z total_points axis (get_coord_point3d axis pivot) min_x max_x min_y max_y min_z max_z left_tr right_tr

-- | Build a KD-Tree out of a set of points
mkKdTree_seq :: Vector Point3d -> KdTree
mkKdTree_seq pts = mkKdTreeWithAxis_seq 0 pts

--------------------------------------------------------------------------------

-- | Maps a list of points to a list of their nearest neighbor.
allNearest_seq :: KdTree -> Vector Point3d -> Vector Point3d
allNearest_seq tr ls =
    map (\p -> nearest tr p) ls

nearest :: KdTree -> Point3d -> Point3d
nearest tr query =
    case tr of
        KdEmpty -> (0.0,0.0,0.0)
        KdLeaf x y z -> (x,y,z)
        KdNode x y z total_points axis split_val min_x max_x min_y max_y min_z max_z left_tr right_tr ->
            let pivot = (x,y,z)
                tst_query = get_coord_point3d axis query
                tst_pivot = get_coord_point3d axis pivot
            in if tst_query .<. tst_pivot
               then find_nearest pivot query tst_pivot tst_query left_tr right_tr
               else find_nearest pivot query tst_pivot tst_query right_tr left_tr

-- | Find the closest point to query in a KD-tree
find_nearest :: Point3d -> Point3d -> Float -> Float -> KdTree -> KdTree -> Point3d
find_nearest pivot query tst_pivot tst_query good_side other_side =
  let best0 = nearest good_side query
      candidate1 = least_dist_point3d query best0 pivot
      -- whether the difference between the splitting coordinate of the search point and current node
      -- is less than the distance (overall coordinates) from the search point to the current best.
      nearest_other_side = tst_query .-. tst_pivot
  in if (nearest_other_side .*. nearest_other_side) .<=. (dist_point3d query candidate1)
     then let candidate2 = nearest other_side query
              best1 = least_dist_point3d query candidate1 candidate2
          in best1
     else candidate1
  -- in let candidate2 = nearest other_side query
  --        best1 = least_dist_point3d query candidate1 candidate2
  --    in best1

-- | Return the point that is closest to a
least_dist_point3d :: Point3d -> Point3d -> Point3d -> Point3d
least_dist_point3d a b c =
  let d1 = dist_point3d a b
      d2 = dist_point3d a c
  in if d1 .<. d2 then b else c

-----------------------------------------------------------------------------------------

-- | Two point correlation
countCorr_seq :: Point3d -> Float -> KdTree -> Int
countCorr_seq probe radius tr =
  case tr of
    KdEmpty -> 0

    KdLeaf x y z ->
      if (dist_point3d probe (x, y, z)) .<. (radius .*. radius)
      then 1
      else 0

    KdNode x y z elems axis split_val min_x max_x min_y max_y min_z max_z left right ->
      -- Ported over from ASTBenchmarks
      let center_x  = (min_x .+. max_x) ./. 2.0
          center_y  = (min_y .+. max_y) ./. 2.0
          center_z  = (min_z .+. max_z) ./. 2.0
          (probe_x, probe_y, probe_z) = probe
          d_x       = probe_x .-. center_x
          d_y       = probe_y .-. center_y
          d_z       = probe_z .-. center_z
          boxdist_x = (max_x .-. min_x) ./. 2.0
          boxdist_y = (max_y .-. min_y) ./. 2.0
          boxdist_z = (max_z .-. min_z) ./. 2.0
          sum       = (d_x .*. d_x) .+. (d_y .*. d_y) .+. (d_z .*. d_z)
          boxsum    = (boxdist_x .*. boxdist_x) .+. (boxdist_y .*. boxdist_y) .+. (boxdist_z .*. boxdist_z)
      in if (sum .-. boxsum) .<. (radius .*. radius)
         then let n1 = countCorr_seq probe radius left
                  n2 = countCorr_seq probe radius right
              in if (dist_point3d probe (x, y, z)) .<. (radius .*. radius)
                 then n1 + n2 + 1
                 else n1 + n2
         else
             if (dist_point3d probe (x, y, z)) .<. (radius .*. radius)
             then 1
             else 0

nCountCorr_seq :: Int -> Float -> Vector Point3d -> KdTree -> (Float, Float, Float, Int)
nCountCorr_seq iters radius pts tr =
    let len = length pts
        i = rand
        j = (mod i len) - 1
        query = nth pts j
        count = countCorr_seq query radius tr
    in if iters <= 0
       then let (qx,qy,qz) = query
            in (qx, qy, qz, count)
       else nCountCorr_seq (iters-1) radius pts tr

allCountCorr_seq :: Float -> KdTree -> Vector Point3d -> Vector Int
allCountCorr_seq radius tr ls =
    map (\query -> countCorr_seq query radius tr) ls

--------------------------------------------------------------------------------

-- | Sum of all points in KD-Tree
sumKdTree :: KdTree -> Float
sumKdTree tr =
  case tr of
    KdEmpty -> 0.0
    KdLeaf x y z -> x .+. y .+. z
    KdNode x y z _ _ _ _ _ _ _ _ _ left right ->
      let o = sumKdTree left
          p = sumKdTree right
      in x .+. y .+. z .+. o .+. p

countLeaves :: KdTree -> Int
countLeaves tr =
  case tr of
    KdEmpty -> 0
    KdLeaf _ _ _ -> 1
    KdNode _ _ _ _ _ _ _ _ _ _ _ _ left right ->
      let o = countLeaves left
          p = countLeaves right
      in o + p

sumList :: Vector Point3d -> Float
sumList ls = foldl (\acc (pt :: Point3d) ->
                        let (x,y,z) = pt
                        in acc .+. x .+. y .+. z)
                   0.0 ls

--------------------------------------------------------------------------------

check_buildkdtree :: Vector Point3d -> KdTree -> ()
check_buildkdtree pts tr =
    let expected = sumList pts
        actual = sumKdTree tr
        err = (expected .-. actual)
        _ = printsym (quote "Expected: ")
        _ = printfloat expected
        _ = printsym (quote "\n")
        _ = printsym (quote "Actual: ")
        _ = printfloat actual
        _ = printsym (quote "\n")
    in print_check (float_abs err .<. 0.1)

check_countcorr :: Vector Point3d -> Point3d -> Int -> Float -> ()
check_countcorr pts query actual radius =
    let radius_sq = radius .*. radius
        expected = foldl (\acc pt  ->
                             if (dist_point3d query pt) .<. radius_sq
                             then acc + 1
                             else acc)
                   0 pts
        _ = printsym (quote "Expected: ")
        _ = printint expected
        _ = printsym (quote "\n")
        _ = printsym (quote "Actual: ")
        _ = printint actual
        _ = printsym (quote "\n")
    in print_check (expected == actual)

check_nearest :: Vector (Float, Float, Float) -> Vector (Float, Float, Float) -> ()
check_nearest pts actual =
    let n = length pts
        idxs = generate n (\i -> i)
        tup = foldl (\(acc :: (Bool, Int)) i ->
                         let pt = nth pts i
                             nn = nth actual i
                             (acc_b, acc_inexact) = acc
                         in if eq_point3d pt nn
                            then (acc_b && True, acc_inexact)
                            else (False, acc_inexact+1))
              (True, 0) idxs
        (is_ok, _inexact) = tup
    in print_check is_ok
