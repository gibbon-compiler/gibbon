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

printPoint :: (Float, Float) -> Int
printPoint tup =
    let a = tup !!! 0
        b = tup !!! 1
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ")")
    in 0

printMassPoint :: (Float, Float, Float) -> Int
printMassPoint tup =
    let a = tup !!! 0
        b = tup !!! 1
        c = tup !!! 2
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ")")
    in 0

printBox :: (Float, Float, Float, Float) -> Int
printBox tup =
    let a = tup !!! 0
        b = tup !!! 1
        c = tup !!! 2
        d = tup !!! 3
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ",")
        _ = printfloat d
        _ = printsym (quote ")")
    in 0

printParticle :: (Float, Float, Float, Float, Float) -> Int
printParticle tup =
    let a = tup !!! 0
        b = tup !!! 1
        c = tup !!! 2
        d = tup !!! 3
        e = tup !!! 4
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
    in 0

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

myprintBHTree :: BH_Tree -> Int
myprintBHTree bht =
    case bht of
        BH_Empty -> printsym (quote "(BH_Empty)")
        BH_Leaf x y m ->
            let _ = printsym (quote "(BH_Leaf")
                _ = printMassPoint (x,y,m)
                _ = printsym (quote ") ")
            in 10
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
            in 10

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
dist a b =
  let a_x = a !!! 0
      a_y = a !!! 1
      b_x = b !!! 0
      b_y = b !!! 1
      d1 = (a_x .-. b_x)
      d2 = (a_y .-. b_y)
  in (d1 .*. d1) .+. (d2 .*. d2)

applyAccel :: (Float, Float, Float, Float, Float) -> (Float, Float) -> (Float, Float, Float, Float, Float)
applyAccel particle accel =
  let vx = particle !!! 3
      vy = particle !!! 4
      ax = accel !!! 0
      ay = accel !!! 1
      -- global constant
      dt = 2.0
  in (particle !!! 0, particle !!! 1, particle !!! 2, vx .+. (ax .*. dt), vy .+. (ay .*. dt))

isClose :: (Float, Float) -> (Float, Float) -> Float -> Bool
isClose a b size =
    let r2 = dist a b
        sizesq = size .*. size
    in r2 .<. sizesq

accel :: (Float, Float, Float) -> Float -> Float -> Float -> (Float, Float)
accel mpt1 x2 y2 m2 =
  let x1 = mpt1 !!! 0
      y1 = mpt1 !!! 1
      m1 = mpt1 !!! 2

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
        let a1 = calcAccel_seq mpt tr1
            a2 = calcAccel_seq mpt tr2
            a3 = calcAccel_seq mpt tr3
            a4 = calcAccel_seq mpt tr4
            x1 = a1 !!! 0
            y1 = a1 !!! 1
            x2 = a2 !!! 0
            y2 = a2 !!! 1
            x3 = a3 !!! 0
            y3 = a3 !!! 1
            x4 = a4 !!! 0
            y4 = a4 !!! 1

        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

calcAccel_par :: Int -> (Float, Float, Float) -> BH_Tree -> (Float, Float)
calcAccel_par cutoff mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass total_pts size tr1 tr2 tr3 tr4 ->
      if isClose (mpt !!! 0, mpt !!! 1) (x, y) size
      then
        if total_pts < cutoff then calcAccel_seq mpt tr else
        let a1 = spawn (calcAccel_par cutoff mpt tr1)
            a2 = spawn (calcAccel_par cutoff mpt tr2)
            a3 = spawn (calcAccel_par cutoff mpt tr3)
            a4 = calcAccel_par cutoff mpt tr4
            _  = sync
            x1 = a1 !!! 0
            y1 = a1 !!! 1
            x2 = a2 !!! 0
            y2 = a2 !!! 1
            x3 = a3 !!! 0
            y3 = a3 !!! 1
            x4 = a4 !!! 0
            y4 = a4 !!! 1
        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

calcCentroid_seq :: Vector (Float, Float, Float) -> (Float, Float, Float)
calcCentroid_seq mpts =
    let lam1 = (\(acc :: (Float, Float, Float)) (mpt :: (Float, Float, Float)) ->
                     let x = mpt !!! 0
                         y = mpt !!! 1
                         m = mpt !!! 2
                         acc_x = acc !!! 0
                         acc_y = acc !!! 1
                         acc_m = acc !!! 2
                     in (acc_x .+. (x.*.m), acc_y .+. (y.*.m), acc_m .+. m))
        sum = foldl
                lam1
                (0.0, 0.0, 0.0)
                mpts
        sum_x = sum !!! 0
        sum_y = sum !!! 1
        sum_m = sum !!! 2
    in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

calcCentroid_par :: Vector (Float, Float, Float) -> (Float, Float, Float)
calcCentroid_par mpts =
    let lam1 = (\(acc :: (Float, Float, Float)) (mpt :: (Float, Float, Float)) ->
                     let x = mpt !!! 0
                         y = mpt !!! 1
                         m = mpt !!! 2
                         acc_x = acc !!! 0
                         acc_y = acc !!! 1
                         acc_m = acc !!! 2
                     in (acc_x .+. (x.*.m), acc_y .+. (y.*.m), acc_m .+. m))
        lam2  = (\(acc1 :: (Float, Float, Float)) (acc2 :: (Float, Float, Float)) ->
                     let x1 = acc1 !!! 0
                         y1 = acc1 !!! 1
                         z1 = acc1 !!! 2
                         x2 = acc2 !!! 0
                         y2 = acc2 !!! 1
                         z2 = acc2 !!! 2
                     in (x1 .+. x2, y1 .+. y2, z1 .+. z2))
        sum = foldl2_par
                lam1
                (0.0, 0.0, 0.0)
                lam2
                mpts
        sum_x = sum !!! 0
        sum_y = sum !!! 1
        sum_m = sum !!! 2
    in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

inBox :: Float -> Float -> Float -> Float -> Float -> Float -> Bool
inBox llx lly rux ruy px py =
    (px .>. llx) && (px .<=. rux) && (py .>. lly) && (py .<=. ruy)

masspointsInBox_seq :: (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
masspointsInBox_seq box mpts =
    filter
      (\(mpt :: (Float, Float, Float)) ->
                  let llx = box !!! 0
                      lly = box !!! 1
                      rux = box !!! 2
                      ruy = box !!! 3
                      x = mpt !!! 0
                      y = mpt !!! 1
                  in  inBox llx lly rux ruy x y)
      mpts

maxDim :: (Float, Float, Float, Float) -> Float
maxDim box =
    let llx = box !!! 0
        lly = box !!! 1
        rux = box !!! 2
        ruy = box !!! 3
    in maxFloat (rux.-.llx) (ruy.-.lly)

buildQtree_seq :: (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> BH_Tree
buildQtree_seq box mpts =
    let len = length mpts
        llx = box !!! 0
        lly = box !!! 1
        rux = box !!! 2
        ruy = box !!! 3
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let mpt = calcCentroid_seq mpts
                x  = mpt !!! 0
                y  = mpt !!! 1
                m  = mpt !!! 2
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
                x = mpt !!! 0
                y = mpt !!! 1
                m = mpt !!! 2
            in BH_Node x y m total_points size tr1 tr2 tr3 tr4

buildQtree_par :: Int -> (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> BH_Tree
buildQtree_par cutoff box mpts =
    let len = length mpts in
    if len < cutoff then buildQtree_seq box mpts else
    let llx = box !!! 0
        lly = box !!! 1
        rux = box !!! 2
        ruy = box !!! 3
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let mpt = calcCentroid_par mpts
                x  = mpt !!! 0
                y  = mpt !!! 1
                m  = mpt !!! 2
            in BH_Leaf x y m
        else
            let mpt = calcCentroid_par mpts
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
                x = mpt !!! 0
                y = mpt !!! 1
                m = mpt !!! 2
            in BH_Node x y m total_points size tr1 tr2 tr3 tr4

oneStep_seq :: (Float, Float, Float, Float)
            -> Vector (Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
oneStep_seq box mpts ps =
    let bht = buildQtree_seq box mpts
        ps2 = generate (length ps)
                       (\i ->
                            let p = nth ps i
                                mpt = nth mpts i
                                accel = calcAccel_seq mpt bht
                            in applyAccel p accel)
        -- _ = debugPrint bht ps2
    in ps2

oneStep_par :: Int
            -> (Float, Float, Float, Float)
            -> Vector (Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
oneStep_par cutoff box mpts ps =
    let bht = buildQtree_par cutoff box mpts
        _ = printsym (quote "tree built")
        ps2 = generate_par (length ps)
                       (\i ->
                            let p = nth ps i
                                mpt = nth mpts i
                                accel = calcAccel_seq mpt bht
                            in applyAccel p accel)
        -- _ = debugPrint bht ps2
    in ps2

debugPrint :: BH_Tree -> Vector (Float, Float, Float, Float, Float) -> Int
debugPrint bht ps2 =
    let _ = myprintBHTree bht
        _ = printsym (quote "\n")
        _ = printVec (\p -> let _ = printParticle p
                                _ = printsym (quote "\n")
                            in  10) ps2
        _ = printsym (quote "\n")
    in 10

--------------------------------------------------------------------------------

pbbs_length :: Float -> Float -> Float
pbbs_length x y = sqrt ((x .*. x) .+. (y .*. y))

calcForces :: Vector (Float, Float, Float, Float, Float)
           -> Int
           -> (Float, Float, Float, Float, Float)
           -> (Float, Float)
calcForces ps idx p_idx =
    let m_idx = p_idx !!! 2
        ax_idx = p_idx !!! 3
        ay_idx = p_idx !!! 4
        gGrav = 1.0
    in ifoldl
      (\(acc :: (Float, Float)) (j :: Int) (p :: (Float, Float, Float, Float, Float)) ->
           if idx == j
           then
               let x = acc !!! 0
                   y = acc !!! 1
               in (x,y)
           else
               let force_x = acc !!! 0
                   force_y = acc !!! 1
                   m_j = p !!! 2
                   ax_j = p !!! 3
                   ay_j = p !!! 4
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
                          ax_idx = p_idx !!! 3
                          ay_idx = p_idx !!! 4
                          forces = calcForces ps idx p_idx
                          force_x = forces !!! 0
                          force_y = forces !!! 1
                          force2_x = force_x .-. ax_idx
                          force2_y = force_y .-. ay_idx
                          e = (pbbs_length force2_x force2_y) ./. (pbbs_length force_x force_y)
                      in err .+. e)
                 0.0
                 outer
    in err1 ./. (intToFloat nCheck)
