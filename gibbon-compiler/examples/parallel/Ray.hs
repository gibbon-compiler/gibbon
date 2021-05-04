{-# LANGUAGE NoImplicitPrelude #-}

module Ray where

import Gibbon.Prelude
import Gibbon.Vector
import Gibbon.Vector.Parallel

import Mergesort
import Geometry

--------------------------------------------------------------------------------

type Point3d = (Float, Float, Float)

type Aabb = ( Float -- min_x
            , Float -- min_y
            , Float -- min_z
            , Float -- max_x
            , Float -- max_y
            , Float -- max_z
            )

print_aabb :: Aabb -> ()
print_aabb aabb =
  let (min_x, min_y, min_z, max_x, max_y, max_z) = aabb
      _ = printsym (quote "{min: ")
      _ = print_point3d (min_x, min_y, min_z)
      _ = printsym (quote ", max: ")
      _ = print_point3d (max_x, max_y, max_z)
      _ = printsym (quote "}")
  in ()

enclosing :: Aabb -> Aabb -> Aabb
enclosing box_a box_b =
  let (a_min_x, a_min_y, a_min_z, a_max_x, a_max_y, a_max_z) = box_a
      (b_min_x, b_min_y, b_min_z, b_max_x, b_max_y, b_max_z) = box_b
      small_x = minFloat a_min_x b_min_x
      small_y = minFloat a_min_y b_min_y
      small_z = minFloat a_min_z b_min_z
      big_x = maxFloat a_max_x b_max_x
      big_y = maxFloat a_max_y b_max_y
      big_z = maxFloat a_max_z b_max_z
  in (small_x, small_y, small_z, big_x, big_y, big_z)

centre :: Aabb -> Point3d
{-# INLINE centre #-}
centre box =
  let (_, _, _, max_x, max_y, max_z) = box
  -- https://github.com/athas/raytracers/issues/10
  in (max_x, max_y, max_z)

--------------------------------------------------------------------------------

type Position = ( Float -- x
                , Float -- y
                , Float -- z
                )

type Direction = ( Float -- x
                 , Float -- y
                 , Float -- z
                 )

type Color = ( Float -- red
             , Float -- green
             , Float -- blue
             )

type Sphere = ( -- Radius
                Float
                -- Position
              , Float -- pos_x
              , Float -- pos_y
              , Float -- pos_z
                -- Color
              , Float -- red
              , Float -- green
              , Float -- blue
              )

print_sphere :: Sphere -> ()
print_sphere s =
  let _ = printsym (quote "{pos: ")
      _ = print_point3d (get_position_sphere s)
      _ = printsym (quote ", colour: ")
      _ = print_point3d (get_color_sphere s)
      _ = printsym (quote ", radius: ")
      _ = printfloat (get_radius_sphere s)
      _ = printsym (quote "}")
  in ()

get_radius_sphere :: Sphere -> Float
{-# INLINE get_radius_sphere #-}
get_radius_sphere sphere =
  let (r,_,_,_,_,_,_) = sphere
  in r

get_position_sphere :: Sphere -> Position
{-# INLINE get_position_sphere #-}
get_position_sphere sphere =
  let (_,px,py,pz,_,_,_) = sphere
  in (px,py,pz)

get_color_sphere :: Sphere -> Color
{-# INLINE get_color_sphere #-}
get_color_sphere sphere =
  let (_,_,_,_,cx,cy,cz) = sphere
  in (cx,cy,cz)

type Ray = ( Float -- pos_x
           , Float -- pos_y
           , Float -- pos_z
           , Float -- dir_x
           , Float -- dir_y
           , Float -- dir_z
           )

get_origin_ray :: Ray -> Point3d
{-# INLINE get_origin_ray #-}
get_origin_ray ray =
  let (px,py,pz,_,_,_) = ray
  in (px,py,pz)

get_dir_ray :: Ray -> Point3d
{-# INLINE get_dir_ray #-}
get_dir_ray ray =
  let (_,_,_,dx,dy,dz) = ray
  in (dx,dy,dz)


point_at_param :: Ray -> Float -> Point3d
{-# INLINE point_at_param #-}
point_at_param ray t =
  let origin = get_origin_ray ray
      dir = get_dir_ray ray
  in add_point3d origin (scale_point3d t dir)

sphere_aabb :: Sphere -> Aabb
sphere_aabb sphere =
  let (radius, px, py, pz, _, _, _) = sphere
      -- (min_x, min_y, min_z) = sub_point3d (px,py,pz) (radius, radius, radius)
      -- (max_x, max_y, max_z) = add_point3d (px,py,pz) (radius, radius, radius)
  in (px .-. radius, py .-. radius, pz .-. radius, px .+. radius, py .+. radius, pz .+. radius)

type Hit = ( -- Shortcut that says whether this is a Just Hit, or a Nothing.
             Bool
             -- t
           , Float
             -- Position
           , Float -- pos_x
           , Float -- pos_y
           , Float -- pos_z
             -- Normal
           , Float -- dir_x
           , Float -- dir_y
           , Float -- dir_z
             -- Color
           , Float -- red
           , Float -- green
           , Float -- blue
           )

-- eq_Hit :: Hit -> Hit -> Bool
-- eq_Hit h1 h2 =
--   let (t_1, px_1, py_1, pz_1, nx_1, ny_1, nz_1, cx_1, cy_1, cz_1) = h1
--       (t_2, px_2, py_2, pz_2, nx_2, ny_2, nz_2, cx_2, cy_2, cz_2) = h2
--   in t_1 .==. t_2 &&
--      px_1 .==. px_2 && py_1 .==. py_2 && pz_1 .==. pz_2 &&
--      nx_1 .==. nx_2 && ny_1 .==. ny_2 && nz_1 .==. nx_2 &&
--      cx_1 .==. cx_2 && cy_1 .==. cy_2 && cz_1 .==. cx_2

mk_not_hit :: Hit
mk_not_hit = (False, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)

get_hit_status :: Hit -> Bool
{-# INLINE get_hit_status #-}
get_hit_status hit =
  let (did_hit,_,_,_,_,_,_,_,_,_,_) = hit
  in did_hit

get_position_hit :: Hit -> Point3d
{-# INLINE get_position_hit #-}
get_position_hit hit =
  let (_,_,pos_x,pos_y,pos_z,_,_,_,_,_,_) = hit
  in (pos_x,pos_y,pos_z)

get_normal_hit :: Hit -> Point3d
{-# INLINE get_normal_hit #-}
get_normal_hit hit =
  let (_,_,_,_,_,dir_x,dir_y,dir_z,_,_,_) = hit
  in (dir_x, dir_y, dir_z)

get_color_hit :: Hit -> Point3d
{-# INLINE get_color_hit #-}
get_color_hit hit =
  let (_,_,_,_,_,_,_,_,r,g,b) = hit
  in (r,g,b)

sphere_hit :: Sphere -> Ray -> Float -> Float -> Hit
sphere_hit sphere ray t_min t_max =
  let dir_ray = get_dir_ray ray
      origin_ray = get_origin_ray ray
      pos_sphere = get_position_sphere sphere
      radius_sphere = get_radius_sphere sphere
      (cx,cy,cz) = get_color_sphere sphere
      oc = sub_point3d origin_ray pos_sphere
      a = dot_point3d dir_ray dir_ray
      b = dot_point3d oc dir_ray
      c = (dot_point3d oc oc) .-. (radius_sphere .*. radius_sphere)
      discriminant = (b .*. b) .-. (a .*. c)
      f = (\temp ->
             if temp .<. t_max && temp .>. t_min
             then
               let point = point_at_param ray temp
                   (px,py,pz) = point
                   (nx,ny,nz) = scale_point3d (1.0 ./. radius_sphere) (sub_point3d point pos_sphere)
               in (True, temp, px, py, pz, nx, ny, nz, cx, cy, cz)
             else mk_not_hit)
  in if discriminant .<=. 0.0
     then mk_not_hit
     else
       let sqrt_v = sqrt discriminant
           hit1 = f (((0.0 .-. b) .-. sqrt_v) ./. a)
       in if get_hit_status hit1
          then hit1
          else f (((0.0 .-. b) .+. sqrt_v) ./. a)

aabb_hit :: Aabb -> Ray -> Float -> Float -> Bool
aabb_hit aabb ray tmin0 tmax0 =
  let iter = (\min' max' origin' dir' tmin' tmax' ->
                let invD = 1.0 ./. dir'
                    t0 = (min' .-. origin') .*. invD
                    t1 = (max' .-. origin') .*. invD
                    tmin'' = maxFloat (if invD .<. 0.0 then t1 else t0) tmin'
                    tmax'' = minFloat (if invD .<. 0.0 then t0 else t1) tmax'
                in (tmin'', tmax''))
      (origin_x, origin_y, origin_z) = get_origin_ray ray
      (dir_x, dir_y, dir_z) = get_dir_ray ray
      (min_x, min_y, min_z, max_x, max_y, max_z) = aabb
      (tmin1, tmax1) = iter min_x max_x origin_x dir_x tmin0 tmax0
  in if tmax1 .<=. tmin1
     then False
     else let (tmin2, tmax2) = iter min_y max_y origin_y dir_y tmin1 tmax1
          in if tmax2 .<=. tmin2
             then False
             else let (tmin3, tmax3) = iter min_z max_z origin_z dir_z tmin2 tmax2
                  in tmax3 .>. tmin3

objs_hit :: Bvh -> Ray -> Float -> Float -> Hit
objs_hit objs ray t_min t_max =
  case objs of
    Bvh_Leaf _min_x _min_y _min_z _max_x _max_y _max_z radius px py pz cr cg cb ->
      sphere_hit (radius, px, py, pz, cr, cg, cb) ray t_min t_max
    Bvh_Split min_x min_y min_z max_x max_y max_z left right ->
      if aabb_hit (min_x, min_y, min_z, max_x, max_y, max_z) ray t_min t_max
      then let hit1 = objs_hit left ray t_min t_max
               hit2 = objs_hit right ray t_min t_max
           in if get_hit_status hit1
              then if get_hit_status hit2
                   then hit2
                   else hit1
              else hit2
      else mk_not_hit

--------------------------------------------------------------------------------

-- Bvh specialized for sphere's.

data Bvh = Bvh_Leaf -- Aabb
                    Float -- min_x
                    Float -- min_y
                    Float -- min_z
                    Float -- max_x
                    Float -- max_y
                    Float -- max_z
                    -- Sphere
                    -- Radius
                    Float
                    -- Position
                    Float -- pos_x
                    Float -- pos_y
                    Float -- pos_z
                    -- Color
                    Float -- red
                    Float -- green
                    Float -- blue

         | Bvh_Split -- Aabb
                     Float -- min_x
                     Float -- min_y
                     Float -- min_z
                     Float -- max_x
                     Float -- max_y
                     Float -- max_z
                     -- Children
                     Bvh
                     Bvh

get_aabb_bvh :: Bvh -> Aabb
get_aabb_bvh bvh =
  case bvh of
    Bvh_Leaf min_x min_y min_z max_x max_y max_z _radius _px _py _pz _cr _cg _cb ->
      (min_x, min_y, min_z, max_x, max_y, max_z)
    Bvh_Split min_x min_y min_z max_x max_y max_z left right ->
      (min_x, min_y, min_z, max_x, max_y, max_z)

print_bvh :: Bvh -> ()
print_bvh bvh =
  case bvh of
    Bvh_Leaf min_x min_y min_z max_x max_y max_z radius px py pz cr cg cb ->
      let _ = printsym (quote "bvh_leaf{sphere: ")
          _ = print_sphere (radius, px, py, pz, cr, cg, cb)
          _ = printsym (quote ", aabb: ")
          _ = print_aabb (min_x, min_y, min_z, max_x, max_y, max_z)
          _ = printsym (quote "}")
      in ()
    Bvh_Split min_x min_y min_z max_x max_y max_z left right ->
      let _ = printsym (quote "bvh_split{left: ")
          _ = print_bvh left
          _ = printsym (quote ", right: ")
          _ = print_bvh right
          _ = printsym (quote ", aabb: ")
          _ = print_aabb (min_x, min_y, min_z, max_x, max_y, max_z)
          _ = printsym (quote "}")
      in ()


countLeavesBvh :: Bvh -> Int
countLeavesBvh bvh =
  case bvh of
    Bvh_Leaf _min_x _min_y _min_z _max_x _max_y _max_z _radius _px _py _pz _cr _cg _cb ->
      1
    Bvh_Split min_x min_y min_z max_x max_y max_z left right ->
      countLeavesBvh left + countLeavesBvh right


mkBvh_seq :: Vector Sphere -> Bvh
mkBvh_seq objs = mkBvh'_seq 0 (length objs) objs

mkBvh'_seq :: Int -> Int -> Vector Sphere -> Bvh
mkBvh'_seq depth n objs =
  if n == 1
  then let sphere = nth objs 0
           (min_x,min_y,min_z,max_x,max_y,max_z) = sphere_aabb sphere
           (radius, px, py, pz, cr, cg, cb) = sphere
           -- _  = print_aabb (min_x,min_y,min_z,max_x,max_y,max_z)
           -- _ = printsym (quote "\n")
           -- _  = print_sphere (radius, px, py, pz, cr, cg, cb)
           -- _ = printsym (quote "\n")
       in Bvh_Leaf min_x min_y min_z max_x max_y max_z radius px py pz cr cg cb
  else let sorted_objs = sort_spheres depth objs
           (left_spheres, right_spheres) = splitAt (div n 2) sorted_objs
           left_n  = length left_spheres
           right_n = length right_spheres
           left_bvh = mkBvh'_seq (depth+1) left_n left_spheres
           right_bvh = mkBvh'_seq (depth+1) right_n right_spheres
           left_aabb = get_aabb_bvh left_bvh
           right_aabb = get_aabb_bvh right_bvh
           (min_x, min_y, min_z, max_x, max_y, max_z) = enclosing left_aabb right_aabb
       in Bvh_Split min_x min_y min_z max_x max_y max_z left_bvh right_bvh

mkBvh_par :: Vector Sphere -> Bvh
mkBvh_par objs = mkBvh'_par 0 (length objs) objs

mkBvh'_par :: Int -> Int -> Vector Sphere -> Bvh
mkBvh'_par depth n objs =
  if n < 100
  then mkBvh'_seq depth n objs
  else if n == 1
  then let sphere = nth objs 0
           (min_x,min_y,min_z,max_x,max_y,max_z) = sphere_aabb sphere
           (radius, px, py, pz, cr, cg, cb) = sphere
       in Bvh_Leaf min_x min_y min_z max_x max_y max_z radius px py pz cr cg cb
  else let sorted_objs = sort_spheres_par depth objs
           (left_spheres, right_spheres) = splitAt (div n 2) sorted_objs
           left_n  = length left_spheres
           right_n = length right_spheres
           left_bvh = spawn (mkBvh'_par (depth+1) left_n left_spheres)
           right_bvh = mkBvh'_par (depth+1) right_n right_spheres
           _ = sync
           left_aabb = get_aabb_bvh left_bvh
           right_aabb = get_aabb_bvh right_bvh
           (min_x, min_y, min_z, max_x, max_y, max_z) = enclosing left_aabb right_aabb
       in Bvh_Split min_x min_y min_z max_x max_y max_z left_bvh right_bvh

--------------------------------------------------------------------------------

cmpx_sphere :: Sphere -> Sphere -> Int
cmpx_sphere s1 s2 =
  let aabb1 = sphere_aabb s1
      aabb2 = sphere_aabb s2
      (cx1,_,_) = centre aabb1
      (cx2,_,_) = centre aabb2
  in compare_float cx1 cx2

cmpy_sphere :: Sphere -> Sphere -> Int
cmpy_sphere s1 s2 =
  let aabb1 = sphere_aabb s1
      aabb2 = sphere_aabb s2
      (_,cy1,_) = centre aabb1
      (_,cy2,_) = centre aabb2
  in compare_float cy1 cy2

cmpz_sphere :: Sphere -> Sphere -> Int
cmpz_sphere s1 s2 =
  let aabb1 = sphere_aabb s1
      aabb2 = sphere_aabb s2
      (_,_,cz1) = centre aabb1
      (_,_,cz2) = centre aabb2
  in compare_float cz1 cz2

sort_spheres :: Int -> Vector Sphere -> Vector Sphere
sort_spheres depth ls =
    let axis = mod depth 3
        ls2 = copy ls in
    if axis == 0
    then inplacevsort ls2 cmpx_sphere
    else if axis == 1
    then inplacevsort ls2 cmpy_sphere
    else inplacevsort ls2 cmpz_sphere

sort_spheres_par :: Int -> Vector Sphere -> Vector Sphere
sort_spheres_par depth ls =
    let axis = mod depth 3 in
    if axis == 0
    then mergeSort cmpx_sphere ls
    else if axis == 1
    then mergeSort cmpy_sphere ls
    else mergeSort cmpz_sphere ls

--------------------------------------------------------------------------------

type Camera = ( -- Origin
                Float -- origin_x
              , Float -- origin_y
              , Float -- origin_z
                -- llc
              , Float -- llc_x
              , Float -- llc_y
              , Float -- llc_z
                -- horizontal
              , Float -- horizontal_x
              , Float -- horizontal_y
              , Float -- horizontal_z
                -- vertical
              , Float -- vertical_x
              , Float -- vertical_y
              , Float -- vertical_z
              )

get_origin_camera :: Camera -> Point3d
get_origin_camera cam =
  let (origin_x, origin_y, origin_z,_,_,_,_,_,_,_,_,_) = cam
  in (origin_x, origin_y, origin_z)

get_llc_camera :: Camera -> Point3d
get_llc_camera cam =
  let (_,_,_, llc_x, llc_y, llc_z,_,_,_,_,_,_) = cam
  in (llc_x, llc_y, llc_z)

get_horizontal_camera :: Camera -> Point3d
get_horizontal_camera cam =
  let (_, _, _, _, _,_, horizontal_x, horizontal_y, horizontal_z,_,_,_) = cam
  in (horizontal_x, horizontal_y, horizontal_z)

get_vertical_camera :: Camera -> Point3d
get_vertical_camera cam =
  let (_,_,_,_,_,_,_,_,_, vertical_x, vertical_y, vertical_z) = cam
  in (vertical_x, vertical_y, vertical_z)

-- Change by hand in C.
mytan :: Float -> Float
mytan x = x

mkCamera :: Position -> Position -> Direction -> Float -> Float -> Camera
mkCamera lookfrom lookat vup vfov aspect =
  let pi = 3.14159265358979312
      theta = (vfov .*. pi) ./. 180.0
      half_height = mytan (theta ./. 2.0)
      half_width = aspect .*. half_height
      origin = lookfrom
      (origin_x, origin_y, origin_z) = origin
      w = normalize_point3d (sub_point3d lookfrom lookat)
      u = normalize_point3d (cross_point3d vup w)
      v = cross_point3d w u
      (llc_x, llc_y, llc_z) =
        (sub_point3d
          (sub_point3d (sub_point3d origin (scale_point3d half_width u)) (scale_point3d half_height v)) w)
      (horizontal_x, horizontal_y, horizontal_z) = scale_point3d (2.0 .*. half_width) u
      (vertical_x, vertical_y, vertical_z) = scale_point3d (2.0 .*. half_height) v
  in (origin_x, origin_y, origin_z, llc_x, llc_y, llc_z, horizontal_x, horizontal_y, horizontal_z, vertical_x, vertical_y, vertical_z)

get_ray :: Camera -> Float -> Float -> Ray
{-# INLINE get_ray #-}
get_ray cam s t =
  let (pos_x, pos_y, pos_z) = get_origin_camera cam
      origin = get_origin_camera cam
      llc = get_llc_camera cam
      horizontal = get_horizontal_camera cam
      vertical = get_vertical_camera cam
      (dir_x, dir_y, dir_z) =
        (sub_point3d
          (add_point3d
            (add_point3d llc (scale_point3d s horizontal))
            (scale_point3d t vertical))
          origin)
  in  (pos_x, pos_y, pos_z, dir_x, dir_y, dir_z)

reflect :: Point3d -> Point3d -> Point3d
reflect v n = sub_point3d v (scale_point3d (2.0 .*. dot_point3d v n) n)


type Scatter = ( -- Shortcut that says whether this is a Just Scatter, or a Nothing.
                 Bool
                 -- Position
               , Float -- pos_x
               , Float -- pos_y
               , Float -- pos_z
                 -- Direction
               , Float -- dir_x
               , Float -- dir_y
               , Float -- dir_z
                 -- Color
               , Float -- red
               , Float -- green
               , Float -- blue
           )

get_scatter_status :: Scatter -> Bool
get_scatter_status scatter1 =
  let (did_scatter,_,_,_,_,_,_,_,_,_) = scatter1
  in did_scatter

get_ray_scatter :: Scatter -> Ray
get_ray_scatter scatter1 =
  let (_,pos_x,pos_y,pos_z,dir_x,dir_y,dir_z,_,_,_) = scatter1
  in (pos_x,pos_y,pos_z,dir_x,dir_y,dir_z)

get_color_scatter :: Scatter -> Color
get_color_scatter scatter1 =
  let (_,_,_,_,_,_,_,r,g,b) = scatter1
  in (r,g,b)

mk_not_scatter :: Scatter
mk_not_scatter = (False,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0)

scatter :: Ray -> Hit -> Scatter
scatter ray hit =
  let dir = get_dir_ray ray
      pos = get_position_hit hit
      normal = get_normal_hit hit
      color = get_color_hit hit

      reflected = reflect (normalize_point3d dir) normal
      scattered_dir = reflected
      scattered_origin = pos
  in if (dot_point3d scattered_dir normal) .>. 0.0
     then let (pos_x,pos_y,pos_z) = scattered_origin
              (dir_x,dir_y,dir_z) = scattered_dir
              (c_r,c_g,c_b) = color
          in (True,pos_x,pos_y,pos_z,dir_x,dir_y,dir_z,c_r,c_g,c_b)
     else mk_not_scatter

black :: Color
black = (0.0, 0.0, 0.0)

white :: Color
white = (1.0, 1.0, 1.0)

ray_color :: Bvh -> Ray -> Int -> Color
ray_color objs ray depth =
  let t_min = 0.001
      t_max = 1000000000.0
      hit = objs_hit objs ray t_min t_max
  in if get_hit_status hit
     then
       let scatter1 = scatter ray hit
       in if get_scatter_status scatter1
          then if depth < 50
               then let scattered = get_ray_scatter scatter1
                        attenuation = get_color_scatter scatter1
                    in mul_point3d attenuation (ray_color objs scattered (depth+1))
               else black
          else black
     else
       let dir = get_dir_ray ray
           (_,y,_) = normalize_point3d dir
           t = 0.5 .*. (y .+. 1.0)
           bg = (0.5, 0.7, 1.0)
       in add_point3d (scale_point3d (1.0 .-. t) white) (scale_point3d t bg)

trace_ray :: Bvh -> Int -> Int -> Camera -> Int -> Int -> Color
{-# INLINE trace_ray #-}
trace_ray objs width height camera j i =
  let u = (intToFloat i) ./. (intToFloat width)
      v = (intToFloat j) ./. (intToFloat height)
      ray = get_ray camera u v
  in ray_color objs ray 0

type Pixel = (Int, Int, Int)

print_pixel :: Pixel -> ()
print_pixel tup =
    let (a,b,c) = tup
        _ = printsym (quote "(")
        _ = printint a
        _ = printsym (quote ",")
        _ = printint b
        _ = printsym (quote ",")
        _ = printint c
        _ = printsym (quote ")")
    in ()

color_to_pixel :: Color -> Pixel
color_to_pixel c =
  let (x,y,z) = c
      ir = floatToInt (255.99 .*. x)
      ig = floatToInt (255.99 .*. y)
      ib = floatToInt (255.99 .*. z)
  in (ir,ig,ib)

mkPixel :: Bvh -> Int -> Int -> Camera -> Int -> (Int, Int, Int)
{-# INLINE mkPixel #-}
mkPixel objs width height camera l =
  let i = mod l width
      j = height - (div l width)
  in color_to_pixel (trace_ray objs width height camera j i)

render_seq :: Bvh -> Int -> Int -> Camera -> Vector Pixel
render_seq objs width height camera =
  generate (height*width) (\l -> mkPixel objs width height camera l)

render_par :: Bvh -> Int -> Int -> Camera -> Vector Pixel
render_par objs width height camera =
  generate_par (height*width) (\l -> mkPixel objs width height camera l)

--------------------------------------------------------------------------------

type Scene = ( -- look_from
               Float -- look_from_x
             , Float -- look_from_y
             , Float -- look_from_z
               -- look_at
             , Float -- look_at_x
             , Float -- look_at_y
             , Float -- look_at_z
               -- fov
             , Float
               -- spheres
             , Vector Sphere
             )

print_scene :: Scene -> ()
print_scene scene =
  let _ = printsym (quote "{look_from: ")
      _ = print_point3d (get_look_from_scene scene)
      _ = printsym (quote ", look_at: ")
      _ = print_point3d (get_look_at_scene scene)
      _ = printsym (quote ", fov: ")
      _ = printfloat (get_fov_scene scene)
      _ = printsym (quote ", spheres: ")
      _ = printVec (\p -> print_sphere p) (get_spheres_scene scene)
      _ = printsym (quote "}")
  in ()

get_look_from_scene :: Scene -> Point3d
get_look_from_scene scene =
  let (x,y,z,_,_,_,_,_) = scene
  in (x,y,z)

get_look_at_scene :: Scene -> Point3d
get_look_at_scene scene =
  let (_,_,_,x,y,z,_,_) = scene
  in (x,y,z)

get_fov_scene :: Scene -> Float
get_fov_scene scene =
  let (_,_,_,_,_,_,fov,_) = scene
  in fov

get_spheres_scene :: Scene -> Vector Sphere
get_spheres_scene scene =
  let (_,_,_,_,_,_,_,spheres) = scene
  in spheres

camera_from_scene :: Int -> Int -> Scene -> Camera
camera_from_scene width height scene =
  let look_from = get_look_from_scene scene
      look_at = get_look_at_scene scene
      fov = get_fov_scene scene
  in mkCamera look_from look_at (0.0, 1.0, 0.0) fov (intToFloat width ./. intToFloat height)

generate_2d :: Int -> Int -> (Int -> Int -> a) -> Vector a
generate_2d m n f =
  -- vconcat (generate m (\j -> generate n (\i -> f j i)))
  let lam3 = (\i j -> f j i)
      lam1 = (\j ->
                let lam2 = (\i -> lam3 i j)
                in generate n lam2)
      lam0 = (\j -> lam1 j)
  in vconcat (generate m lam0)

rgbbox :: () -> Scene
rgbbox _ =
  let n = 10
      k = 60.0

      leftwall = generate_2d n n (\y z ->
                                   let neg_k = (0.0 .-. k)
                                       pos_x = neg_k ./. 2.0
                                       pos_y = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat y)
                                       pos_z = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat z)
                                       -- (c_r, c_g, c_b) = (1.0, 0.0, 0.0)
                                       radius = k ./. ((intToFloat n) .*. 2.0)
                                   in (radius,pos_x,pos_y,pos_z,1.0,0.0,0.0))
      midwall = generate_2d n n (\x y ->
                                   let neg_k = (0.0 .-. k)
                                       pos_x = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat x)
                                       pos_y = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat y)
                                       pos_z = neg_k ./. 2.0
                                       -- (c_r, c_g, c_b) = (1.0, 1.0, 0.0)
                                       radius = k ./. ((intToFloat n) .*. 2.0)
                                   in (radius,pos_x,pos_y,pos_z,1.0,1.0,0.0))

      rightwall = generate_2d n n (\y z ->
                                   let neg_k = (0.0 .-. k)
                                       pos_x = k ./. 2.0
                                       pos_y = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat y)
                                       pos_z = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat z)
                                       -- (c_r, c_g, c_b) = (0.0, 0.0, 1.0)
                                       radius = k ./. ((intToFloat n) .*. 2.0)
                                   in (radius,pos_x,pos_y,pos_z,0.0,0.0,1.0))

      bottom = generate_2d n n (\x z ->
                                   let neg_k = (0.0 .-. k)
                                       pos_x = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat x)
                                       pos_y = neg_k ./. 2.0
                                       pos_z = (neg_k ./. 2.0) .+. ((k ./. (intToFloat n)) .*. intToFloat z)
                                       -- (c_r, c_g, c_b) = (1.0, 1.0, 1.0)
                                       radius = k ./. ((intToFloat n) .*. 2.0)
                                   in (radius,pos_x,pos_y,pos_z,1.0,1.0,1.0))

      -- This triggers a bug in the compiler.
      -- spheres = append (append leftwall midwall) (append rightwall bottom)
      -- Workaround:
      spheres0 :: Vector (Vector Sphere)
      spheres0 = valloc 4
      spheres1 = inplacevupdate spheres0 0 leftwall
      spheres2 = inplacevupdate spheres1 1 midwall
      spheres3 = inplacevupdate spheres2 2 rightwall
      spheres4 = inplacevupdate spheres3 3 bottom
      spheres = vconcat spheres4

      look_from_x = 0.0
      look_from_y = 30.0
      look_from_z = 30.0
      look_at_x = 0.0
      look_at_y = (0.0 .-. 1.0)
      look_at_z = (0.0 .-. 1.0)
      fov = 75.0
  in (look_from_x,look_from_y,look_from_z,look_at_x,look_at_y,look_at_z,fov,spheres)

irreg :: () -> Scene
irreg _ =
  let n = 100
      k = 600.0
      bottom = generate_2d n n (\x z ->
                                  let pos_x = ((0.0 .-. k) ./. 2.0) .+. ((k ./. intToFloat n) .*. intToFloat x)
                                      pos_y = 0.0
                                      pos_z = ((0.0 .-. k) ./. 2.0) .+. ((k ./. intToFloat n) .*. intToFloat z)
                                      (c_r,c_g,c_b) =  white
                                      radius = k ./. (intToFloat n .*. 2.0)
                                  in (radius,pos_x,pos_y,pos_z,c_r,c_g,c_b))
      look_from_x = 0.0
      look_from_y = 12.0
      look_from_z = 30.0
      look_at_x = 0.0
      look_at_y = 10.0
      look_at_z = 0.0 .-. 1.0
      fov = 75.0
  in (look_from_x,look_from_y,look_from_z,look_at_x,look_at_y,look_at_z,fov,bottom)


--------------------------------------------------------------------------------

gibbon_main =
  let size = sizeParam
      height = size
      width = size
      -- scene = irreg ()
      scene = rgbbox ()
      spheres = get_spheres_scene scene
      objs1 = iterate (mkBvh_seq spheres)
      -- _ = print_bvh objs1
      -- -- objs2 = iterate (mkBvh_par spheres)
      cam = camera_from_scene width height scene
      pixels = iterate (render_seq objs1 width height cam)
      -- pixels2 = iterate (render_par objs1 width height cam)
  in countLeavesBvh objs1
