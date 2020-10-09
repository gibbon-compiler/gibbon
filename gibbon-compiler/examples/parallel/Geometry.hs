module Geomerty where

import MergeSort

--------------------------------------------------------------------------------
-- 3d points
--------------------------------------------------------------------------------

type Point3d = (Float, Float, Float)

print_point3d :: Point3d -> ()
print_point3d tup =
    let (a,b,c) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ")")
    in ()

get_coord_point3d :: Int -> Point3d -> Float
get_coord_point3d axis pt =
  if axis == 0
  then pt !!! 0
  else if axis == 1
  then pt !!! 1
  else pt !!! 2

-- | Distance between two points
dist_point3d :: Point3d -> Point3d -> Float
dist_point3d a b =
  let (a_x, a_y, a_z) = a
      (b_x, b_y, b_z) = b
      d1 = (a_x .-. b_x)
      d2 = (a_y .-. b_y)
      d3 = (a_z .-. b_z)
  in (d1 .*. d1) .+. (d2 .*. d2) .+. (d3 .*. d3)


getNextAxis_3d :: Int -> Int
getNextAxis_3d i = mod (i + 1) 2

eq_point3d :: Point3d -> Point3d -> Bool
eq_point3d a b =
    let (ax,ay,az) = a
        (bx,by,bz) = b
    in ax .==. bx && ay .==. by && az .==. bz

cmpx_point3d :: Point3d -> Point3d -> Int
cmpx_point3d a b =
    let (ax,_,_) = a
        (bx,_,_) = b
    in floatToInt (ax .-. bx)

cmpy_point3d :: Point3d -> Point3d -> Int
cmpy_point3d a b =
    let (_,ay,_) = a
        (_,by,_) = b
    in floatToInt (ay .-. by)

cmpz_point3d :: Point3d -> Point3d -> Int
cmpz_point3d a b =
    let (_,_,az) = a
        (_,_,bz) = b
    in floatToInt (az .-. bz)

add_point3d ::  Point3d -> Point3d -> Point3d
add_point3d a b =
  let (ax,ay,az) = a
      (bx,by,bz) = b
  in (ax .+. bx, ay .+. by, az .+. bz)

sub_point3d ::  Point3d -> Point3d -> Point3d
sub_point3d a b =
  let (ax,ay,az) = a
      (bx,by,bz) = b
  in (ax .-. bx, ay .-. by, az .-. bz)

mul_point3d ::  Point3d -> Point3d -> Point3d
mul_point3d a b =
  let (ax,ay,az) = a
      (bx,by,bz) = b
  in (ax .*. bx, ay .*. by, az .*. bz)

div_point3d ::  Point3d -> Point3d -> Point3d
div_point3d a b =
  let (ax,ay,az) = a
      (bx,by,bz) = b
  in (ax ./. bx, ay ./. by, az ./. bz)

scale_point3d :: Float -> Point3d -> Point3d
scale_point3d s p =
  let (x,y,z) = p
  in (x .*. s, y .*. s, z .*. s)

dot_point3d :: Point3d -> Point3d -> Float
dot_point3d p1 p2 =
  let (x,y,z) = mul_point3d p1 p2
  in x .+. y .+. z

norm_point3d :: Point3d -> Float
norm_point3d p = sqrt (dot_point3d p p)

normalize_point3d :: Point3d -> Point3d
normalize_point3d p = scale_point3d (1.0 ./. (norm_point3d p)) p

cross_point3d :: Point3d -> Point3d -> Point3d
cross_point3d a b =
  let (ax,ay,az) = a
      (bx,by,bz) = b
      cx = (ay .*. bz) .-. (az .*. by)
      cy = (az .*. bx) .-. (ax .*. bz)
      cz = (ax .*. by) .-. (ay .*. bx)
  in (cx, cy, cz)

sort_point3d :: Int -> Vector Point3d -> Vector Point3d
sort_point3d axis ls =
    let ls2 = copy ls in
    if axis == 0
    then inplacevsort ls2 cmpx_point3d
    else if axis == 1
    then inplacevsort ls2 cmpy_point3d
    else inplacevsort ls2 cmpz_point3d

-- sort_point3d :: Int -> Vector Point3d -> Vector Point3d
-- sort_point3d axis ls =
--     if axis == 0
--     then mergeSort_seq cmpx_point3d ls
--     else if axis == 1
--     then mergeSort_seq cmpy_point3d ls
--     else mergeSort_seq cmpz_point3d ls


-- sort_point3d_par :: Int -> Vector Point3d -> Vector Point3d
-- sort_point3d_par axis ls =
--     let ls2 = copy_par ls in
--     if axis == 0
--     then inplacevsort ls2 cmpx_point3d
--     else if axis == 1
--     then inplacevsort ls2 cmpy_point3d
--     else inplacevsort ls2 cmpz_point3d

sort_point3d_par :: Int -> Vector Point3d -> Vector Point3d
sort_point3d_par axis ls =
    if axis == 0
    then mergeSort cmpx_point3d ls
    else if axis == 1
    then mergeSort cmpy_point3d ls
    else mergeSort cmpz_point3d ls

--------------------------------------------------------------------------------
-- 2d points
--------------------------------------------------------------------------------

type Point2d = (Float, Float)

print_point2d :: Point2d -> ()
print_point2d tup =
    let (a,b) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ")")
    in ()

-- | Distance between two points
dist_point2d :: Point2d -> Point2d -> Float
{-# INLINE dist_point2d #-}
dist_point2d a b =
  let (a_x, a_y) = a
      (b_x, b_y) = b
      d1 = (a_x .-. b_x)
      d2 = (a_y .-. b_y)
  in (d1 .*. d1) .+. (d2 .*. d2)
