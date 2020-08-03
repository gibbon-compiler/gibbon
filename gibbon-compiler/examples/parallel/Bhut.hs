module Bhut where

import Gibbon.Prelude
import Gibbon.Vector
import Gibbon.Vector.Parallel

{-

type MassPoint = ( Float -- ^ x coord
                 , Float -- ^ y coord
                 , Float -- ^ mass
                 )

type Particle  = ( Float -- ^ x coord
                 , Float -- ^ y coord
                 , Float -- ^ mass
                 , Float -- ^ velocity x
                 , Float -- ^ velocity y
                 )

type Box = ( Float, Float, Float, Float)

-}

printPoint :: (Float, Float) -> ()
printPoint tup =
    let (a,b) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ")")
    in ()

printMassPoint :: (Float, Float, Float) -> ()
printMassPoint tup =
    let (a,b,c) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ")")
    in ()

printBox :: (Float, Float, Float, Float) -> ()
printBox tup =
    let (a,b,c,d) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ",")
        _ = printfloat d
        _ = printsym (quote ")")
    in ()

printParticle :: (Float, Float, Float, Float, Float) -> ()
printParticle tup =
    let (a,b,c,d,e) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ",")
        _ = printfloat d
        _ = printsym (quote ",")
        _ = printfloat e
        _ = printsym (quote ")")
    in ()

data BH_Tree = BH_Empty
             | BH_Leaf Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass
             | BH_Node Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass
                       Int     -- ^ total points
                       Float   -- ^ Size (max_dim box)
                       BH_Tree -- ^ north-west
                       BH_Tree -- ^ north-east
                       BH_Tree -- ^ south-east
                       BH_Tree -- ^ south-west

myprintBHTree :: BH_Tree -> ()
myprintBHTree bht =
    case bht of
        BH_Empty ->
            let _ = printsym (quote "(BH_Empty)")
            in ()
        BH_Leaf x y m ->
            let _ = printsym (quote "(BH_Leaf")
                _ = printMassPoint (x,y,m)
                _ = printsym (quote ") ")
            in ()
        BH_Node x y m total size tr1 tr2 tr3 tr4->
            let _ = printsym (quote "(BH_Node")
                _ = printMassPoint (x,y,m)
                _ = printint total
                _ = printsym (quote " ")
                _ = printfloat size
                _ = printsym (quote " ")
                _ = myprintBHTree tr1
                _ = myprintBHTree tr2
                _ = myprintBHTree tr3
                _ = myprintBHTree tr4
                _ = printsym (quote ") ")
            in ()

getX :: BH_Tree -> Float
getX tr =
  case tr of
    BH_Empty                  -> 0.0
    BH_Leaf x _ _             -> x
    BH_Node x _ _ _ _ _ _ _ _ -> x

getY :: BH_Tree -> Float
getY tr =
  case tr of
    BH_Empty                  -> 0.0
    BH_Leaf _ y _             -> y
    BH_Node _ y _ _ _ _ _ _ _ -> y

getTotalPoints :: BH_Tree -> Int
getTotalPoints tr =
  case tr of
    BH_Empty                  -> 0
    BH_Leaf _ _ _             -> 1
    BH_Node _ _ _ n _ _ _ _ _ -> n

-- | Distance between two points
dist :: (Float, Float) -> (Float, Float) -> Float
{-# INLINE dist #-}
dist a b =
  let (a_x, a_y) = a
      (b_x, b_y) = b
      d1 = (a_x .-. b_x)
      d2 = (a_y .-. b_y)
  in (d1 .*. d1) .+. (d2 .*. d2)

applyAccel :: (Float, Float, Float, Float, Float) -> (Float, Float) -> (Float, Float, Float, Float, Float)
{-# INLINE applyAccel #-}
applyAccel particle accel =
  let (x,y,m,vx,vy) = particle
      (ax,ay) = accel
      -- global constant
      dt = 2.0
  in (x, y, m, vx .+. (ax .*. dt), vy .+. (ay .*. dt))

isClose :: (Float, Float) -> (Float, Float) -> Float -> Bool
{-# INLINE isClose #-}
isClose a b size =
    let r2 = dist a b
        sizesq = size .*. size
    in r2 .<. sizesq

accel :: (Float, Float, Float) -> Float -> Float -> Float -> (Float, Float)
{-# INLINE accel #-}
accel mpt1 x2 y2 m2 =
  let (x1,y1,m1) = mpt1
  in if (x1 .==. x2) && (y1 .==. y2) && (m1 .==. m2)
     then (0.0, 0.0)
     else
       let dx = x1 .-. x2
           dy = y1 .-. y2
           rsqr = (dx .*. dx) .+. (dy .*. dy)
           r = sqrt rsqr
           s = (m1 .*. m2 ./. (rsqr .*. r))
       in (dx .*. s, dy .*. s)

-- the acceleration of a mass point after applying the force applied by surrounding
-- mass points
calcAccel_seq :: (Float, Float, Float) -> BH_Tree -> (Float, Float)
calcAccel_seq mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass total_pts size tr1 tr2 tr3 tr4 ->
      if isClose (mpt !!! 0, mpt !!! 1) (x, y) size
      then
        let (x1,y1) = calcAccel_seq mpt tr1
            (x2,y2) = calcAccel_seq mpt tr2
            (x3,y3) = calcAccel_seq mpt tr3
            (x4,y4) = calcAccel_seq mpt tr4
        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

{-

calcAccel_par :: Int -> (Float, Float, Float) -> BH_Tree -> (Float, Float)
calcAccel_par cutoff mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass total_pts size tr1 tr2 tr3 tr4 ->
      if isClose (mpt !!! 0, mpt !!! 1) (x, y) size
      then
        if total_pts < cutoff then calcAccel_seq mpt tr else
        let (x1,y1) = spawn (calcAccel_par cutoff mpt tr1)
            (x2,y2) = spawn (calcAccel_par cutoff mpt tr2)
            (x3,y3) = spawn (calcAccel_par cutoff mpt tr3)
            (x4,y4) = calcAccel_par cutoff mpt tr4
            _  = sync
        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

-}

calcCentroid_seq :: Vector (Float, Float, Float) -> (Float, Float, Float)
calcCentroid_seq mpts =
    let lam1 = (\(acc :: (Float, Float, Float)) (mpt :: (Float, Float, Float)) ->
                     let (x,y,m) = mpt
                         (acc_x, acc_y, acc_m) = acc
                     in (acc_x .+. (x.*.m), acc_y .+. (y.*.m), acc_m .+. m))
        sum = foldl
                lam1
                (0.0, 0.0, 0.0)
                mpts
        (sum_x, sum_y, sum_m) = sum
    in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

{-

calcCentroid_par :: Vector (Float, Float, Float) -> (Float, Float, Float)
calcCentroid_par mpts =
    let lam1 = (\(acc :: (Float, Float, Float)) (mpt :: (Float, Float, Float)) ->
                     let (x,y,m) = mpt
                         (acc_x, acc_y, acc_m) = acc
                     in (acc_x .+. (x.*.m), acc_y .+. (y.*.m), acc_m .+. m))
        lam2  = (\(acc1 :: (Float, Float, Float)) (acc2 :: (Float, Float, Float)) ->
                     let (x1,y1,z1) = acc1
                         (x2,y2,z2) = acc2
                     in (x1 .+. x2, y1 .+. y2, z1 .+. z2))
        sum = foldl2_par
                lam1
                (0.0, 0.0, 0.0)
                lam2
                mpts
        (sum_x, sum_y, sum_m) = sum
    in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

-}

inBox :: Float -> Float -> Float -> Float -> Float -> Float -> Bool
{-# INLINE inBox #-}
inBox llx lly rux ruy px py =
    (px .>. llx) && (px .<=. rux) && (py .>. lly) && (py .<=. ruy)

-- Parallelize...
masspointsInBox_seq :: (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
masspointsInBox_seq box mpts =
    filter
      (\(mpt :: (Float, Float, Float)) ->
                  let (llx,lly,rux,ruy) = box
                      (x,y) = mpt
                  in  inBox llx lly rux ruy x y)
      mpts

maxDim :: (Float, Float, Float, Float) -> Float
{-# INLINE maxDim #-}
maxDim box =
    let (llx,lly,rux,ruy) = box
    in maxFloat (rux.-.llx) (ruy.-.lly)

buildQtree_seq :: (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> BH_Tree
buildQtree_seq box mpts =
    let len = length mpts
        (llx,lly,rux,ruy) = box
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let (x,y,m) = calcCentroid_seq mpts
            in BH_Leaf x y m
        else
            let mpt = calcCentroid_seq mpts
                midx = (llx .+. rux) ./. 2.0
                midy = (lly .+. ruy) ./. 2.0
                b1 = (llx, lly, midx, midy)
                b2 = (llx, midy, midx, ruy)
                b3 = (midx, midy, rux, ruy)
                b4 = (midx, lly, rux, midy)
                p1 = masspointsInBox_seq b1 mpts
                tr1 = buildQtree_seq b1 p1
                p2 = masspointsInBox_seq b2 mpts
                tr2 = buildQtree_seq b2 p2
                p3 = masspointsInBox_seq b3 mpts
                tr3 = buildQtree_seq b3 p3
                p4 = masspointsInBox_seq b4 mpts
                tr4 = buildQtree_seq b4 p4
                total_points =
                    (getTotalPoints tr1) + (getTotalPoints tr2) +
                    (getTotalPoints tr3) + (getTotalPoints tr4)
                size = maxDim box
                (x,y,m) = mpt
            in BH_Node x y m total_points size tr1 tr2 tr3 tr4

buildQtree_par :: Int -> (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> BH_Tree
buildQtree_par cutoff box mpts =
    let len = length mpts in
        -- _ = printsym (quote "cutoff=")
        -- _ = printint cutoff
        -- _ = printsym (quote "\n") in
    if len < cutoff then buildQtree_seq box mpts else
    let (llx,lly,rux,ruy) = box
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let (x,y,m) = calcCentroid_seq mpts
            in BH_Leaf x y m
        else
            let (x,y,m) = calcCentroid_seq mpts
                midx = (llx .+. rux) ./. 2.0
                midy = (lly .+. ruy) ./. 2.0
                b1 = (llx, lly, midx, midy)
                b2 = (llx, midy, midx, ruy)
                b3 = (midx, midy, rux, ruy)
                b4 = (midx, lly, rux, midy)
                p1 = masspointsInBox_seq b1 mpts
                tr1 = spawn (buildQtree_par cutoff b1 p1)
                p2 = masspointsInBox_seq b2 mpts
                tr2 = spawn (buildQtree_par cutoff b2 p2)
                p3 = masspointsInBox_seq b3 mpts
                tr3 = spawn (buildQtree_par cutoff b3 p3)
                p4 = masspointsInBox_seq b4 mpts
                tr4 = buildQtree_par cutoff b4 p4
                _ = sync
                total_points =
                    (getTotalPoints tr1) + (getTotalPoints tr2) +
                    (getTotalPoints tr3) + (getTotalPoints tr4)
                size = maxDim box
            in BH_Node x y m total_points size tr1 tr2 tr3 tr4


debugPrint :: BH_Tree -> Vector (Float, Float, Float, Float, Float) -> ()
debugPrint bht ps2 =
    let _ = myprintBHTree bht
        _ = printsym (quote "\n")
        _ = printVec (\p -> let _ = printParticle p
                                _ = printsym (quote "\n")
                            in ()) ps2
        _ = printsym (quote "\n")
    in ()

--------------------------------------------------------------------------------

pbbs_length :: Float -> Float -> Float
pbbs_length x y = sqrt ((x .*. x) .+. (y .*. y))

calcForces :: Vector (Float, Float, Float, Float, Float)
           -> Int
           -> (Float, Float, Float, Float, Float)
           -> (Float, Float)
calcForces ps idx p_idx =
    let (m_idx, ax_idx, ay_idx) = p_idx
        gGrav = 1.0
    in ifoldl
      (\(acc :: (Float, Float)) (j :: Int) (p :: (Float, Float, Float, Float, Float)) ->
           if idx == j
           then
               let (x,y) = acc
               in (x,y)
           else
               let (force_x, force_y) = acc
                   (_,_,m_j, ax_j, ay_j) = p
                   v_x = ax_j .-. ax_idx
                   v_y = ay_j .-. ay_idx
                   r = pbbs_length v_x v_y
                   s = m_j .*. m_idx .*. (gGrav ./. (r .*. r .*. r))
                   v2_x = v_x .*. s
                   v2_y = v_x .*. s
               in (force_x .+. v2_x, force_y .+. v2_y))
      (0.0, 0.0)
      ps


check :: Vector (Float, Float, Float, Float, Float) -> Float
check ps =
    let nCheck = 10
        gGrav = 1.0
        outer = generate nCheck (\i -> i)
        err1 = foldl
                 (\err i ->
                      let idx = if i == 0 then 0 else i-1
                          p_idx = nth ps idx
                          (_,_,_,ax_idx, ay_idx) = p_idx
                          (force_x, force_y) = calcForces ps idx p_idx
                          force2_x = force_x .-. ax_idx
                          force2_y = force_y .-. ay_idx
                          e = (pbbs_length force2_x force2_y) ./. (pbbs_length force_x force_y)
                      in err .+. e)
                 0.0
                 outer
    in err1 ./. (intToFloat nCheck)
