-- | It's a 3D tree right now
module KdTree where

--------------------------------------------------------------------------------
-- Lists and sorting

data Point3D = Point3D Int -- ^ x
                       Int -- ^ y
                       Int -- ^ z
    deriving Show

coord3D :: Int -> Point3D -> Int
coord3D axis p =
    case p of
      Point3D x y z ->
          if axis == 0
          then x
          else if axis == 1
          then y
          else z

getNextAxis_3D :: Int -> Int
getNextAxis_3D i = mod (i + 1) 3

data List_Point3D = Cons Point3D List_Point3D
                  | Nil
  deriving Show

length_List_Point3D :: List_Point3D -> Int
length_List_Point3D ls =
    case ls of
        Nil        -> 0
        Cons _ rst -> 1 + (length_List_Point3D rst)

nth_List_Point3D :: Int -> List_Point3D -> Point3D
nth_List_Point3D n ls =
    case ls of
        Nil        -> Point3D 0 0 0
        Cons x rst ->
            if n == 0
            then x
            else nth_List_Point3D (n-1) rst

take_List_Point3D :: Int -> List_Point3D -> List_Point3D
take_List_Point3D n ls =
    case ls of
        Nil        -> Nil
        Cons y rst ->
            if n == 0
            then Nil
            else Cons y (take_List_Point3D (n-1) rst)

drop_List_Point3D :: Int -> List_Point3D -> List_Point3D
drop_List_Point3D n ls =
    case ls of
        Nil        -> Nil
        Cons y rst ->
            if n == 0
            then Cons y rst
            else drop_List_Point3D (n-1) rst

less_than_Point3D :: Int -> Point3D -> Point3D -> Bool
less_than_Point3D axis p1 p2 =
  let a = coord3D axis p1
      b = coord3D axis p2
  in a < b

less_than_List_Point3D :: Int -> Point3D -> List_Point3D -> List_Point3D
less_than_List_Point3D axis pt ls =
    case ls of
        Nil -> Nil
        Cons q rst ->
            if less_than_Point3D axis q pt
            then Cons q (less_than_List_Point3D axis pt rst)
            else (less_than_List_Point3D axis pt rst)

greater_eq_Point3D :: Int -> Point3D -> Point3D -> Bool
greater_eq_Point3D axis p1 p2 =
  let a = coord3D axis p1
      b = coord3D axis p2
  in a >= b

greater_eq_List_Point3D :: Int -> Point3D -> List_Point3D -> List_Point3D
greater_eq_List_Point3D axis pt ls =
    case ls of
        Nil -> Nil
        Cons q rst ->
            if greater_eq_Point3D axis q pt
            then Cons q (greater_eq_List_Point3D axis pt rst)
            else (greater_eq_List_Point3D axis pt rst)

append_List_Point3D :: List_Point3D -> List_Point3D -> List_Point3D
append_List_Point3D xs ys =
    case xs of
        Nil       -> ys
        Cons z zs -> Cons z (append_List_Point3D zs ys)

qsort_List_Point3D :: Int -> List_Point3D -> List_Point3D
qsort_List_Point3D axis ls =
    case ls of
        Nil       -> Nil
        Cons y ys ->
            let lesser  = less_than_List_Point3D axis y ys
                greater = greater_eq_List_Point3D axis y ys
                left  = qsort_List_Point3D axis lesser
                right = qsort_List_Point3D axis greater
            in append_List_Point3D left (Cons y right)

--------------------------------------------------------------------------------
-- The main algorithm

data KdTree  = KdNode Int     -- ^ axis
                      Point3D -- ^ point
                      KdTree  -- ^ left
                      KdTree  -- ^ right
             | KdEmpty
  deriving Show

fromList :: List_Point3D -> KdTree
fromList pts = fromListWithAxis 0 pts

fromListWithAxis :: Int -> List_Point3D -> KdTree
fromListWithAxis axis pts =
    case pts of
        Nil -> KdEmpty
        Cons _ _ ->
            let sorted_pts = qsort_List_Point3D axis pts
                len        = length_List_Point3D pts
                pivot_idx  = div len 2
                pivot      = nth_List_Point3D pivot_idx sorted_pts
                left_pts   = take_List_Point3D pivot_idx sorted_pts
                right_pts  = drop_List_Point3D (pivot_idx+1) sorted_pts
                next_axis  = getNextAxis_3D axis
                left_tr    = fromListWithAxis next_axis left_pts
                right_tr   = fromListWithAxis next_axis right_pts
            in KdNode axis pivot left_tr right_tr


gibbon_main =
    let p1 = Point3D 1 1 1
        p2 = Point3D 2 2 2
        p3 = Point3D 3 3 3
        ls = Cons p1 (Cons p2 (Cons p3 Nil))
        -- tr = fromList ls
        ls2 = qsort_List_Point3D 0 ls
    in 10
