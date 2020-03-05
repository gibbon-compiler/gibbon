module Seq2DBHut where

-- Ported from : https://smlnj-gitlab.cs.uchicago.edu/manticore/pmlc/blob/15539f76c33fdef2ac7fd5d4396213e06732e660/src/benchmarks/programs/barnes-hut/barnes-hut-seq.pml

--------------------------------------------------------------------------------

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

-}

data BH_Tree = BH_Empty
             | BH_Leaf Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass

             | BH_Node Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass
                       BH_Tree -- ^ north-west
                       BH_Tree -- ^ north-east
                       BH_Tree -- ^ south-east
                       BH_Tree -- ^ south-west

getX :: BH_Tree -> Float
getX tr =
  case tr of
    BH_Empty              -> 0.0
    BH_Leaf x _ _         -> x
    BH_Node x _ _ _ _ _ _ -> x

getY :: BH_Tree -> Float
getY tr =
  case tr of
    BH_Empty              -> 0.0
    BH_Leaf _ y _         -> y
    BH_Node _ y _ _ _ _ _ -> y


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
  in (particle !!! 0, particle !!! 1, particle !!! 2, (vx .+. ax) .*. dt, (vy .+. ay) .*. dt)

isClose :: (Float, Float) -> (Float, Float) -> Bool
isClose a b =
  -- global constant
  let eClose = 0.01
  in (dist a b) .<. eClose


accel :: (Float, Float, Float) -> Float -> Float -> Float -> (Float, Float)
accel a x y m =
  let d1   = (a !!! 0) .-. x
      d2   = (a !!! 1) .-. y
      rsqr = (d1 .*. d1) .+. (d2 .*. d2)
      r    = sqrt rsqr
      -- global constant
      epsilon = 0.05
  in if r .<. epsilon
     then (0.0, 0.0)
     else let aabs = m ./. rsqr
          in (aabs .*. d1 ./. r , aabs .*. d2 ./. r)


-- the acceleration of a mass point after applying the force applied by surrounding
-- mass points
calcAccel :: (Float, Float, Float) -> BH_Tree -> (Float, Float)
calcAccel mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass tr1 tr2 tr3 tr4 ->
      if isClose (mpt !!! 0, mpt !!! 1) (x, y)
      then
        let a1 = calcAccel mpt tr1
            x1 = a1 !!! 0
            y1 = a1 !!! 1

            a2 = calcAccel mpt tr2
            x2 = a2 !!! 0
            y2 = a2 !!! 1

            a3 = calcAccel mpt tr3
            x3 = a3 !!! 0
            y3 = a3 !!! 1

            a4 = calcAccel mpt tr4
            x4 = a4 !!! 0
            y4 = a4 !!! 1

        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass


circlePlus_mpt :: (Float, Float, Float) -> Float -> Float -> Float -> (Float, Float, Float)
circlePlus_mpt a x y mass =
  ((a !!! 0) .+. x, (a !!! 1) .+. y, (a !!! 2) .+. mass)


circlePlus :: [(Float, Float, Float)] -> Int -> Int -> Float -> Float -> Float -> (Float, Float, Float)
circlePlus mpts idx stop acc_x acc_y acc_mass =
  if idx == stop
  then (acc_x, acc_y, acc_mass)
  else let pt        = vnth idx mpts
           acc1      = circlePlus_mpt pt acc_x acc_y acc_mass
           acc_x1    = acc1 !!! 0
           acc_y1    = acc1 !!! 1
           acc_mass1 = acc1 !!! 2
       in circlePlus mpts (idx+1) stop acc_x1 acc_y1 acc_mass1


-- calcCentroid :: [MassPoint] -> [MassPoint]
calcCentroid :: [(Float, Float, Float)] -> (Float, Float, Float)
calcCentroid mpts =
  let len = vlength mpts
      acc = circlePlus mpts 0 len 0.0 0.0 0.0
      sum_x    = acc !!! 0
      sum_y    = acc !!! 1
      sum_mass = acc !!! 2
  in (sum_x ./. sum_mass, sum_y ./. sum_mass, sum_mass)


inBox :: Float -> Float -> Float -> Float -> Float -> Float -> Bool
inBox llx lly rux ruy px py =
    if (px .>. llx) && (px .<=. rux) && (py .>. lly) && (py .<=. ruy)
    then True
    else False


massPtsInBox0 :: [(Float, Float, Float)] -> Int -> Int -> Float -> Float -> Float -> Float -> [(Float, Float, Float)] -> [(Float, Float, Float)]
massPtsInBox0 mpts idx stop llx lly rux ruy acc =
  if idx == stop
  then acc
  else
    let pt = vnth idx mpts
    in if inBox llx lly rux ruy (pt !!! 0) (pt !!! 1)
       then let _ = inplacevsnoc acc pt
            in massPtsInBox0 mpts (idx+1) stop llx lly rux ruy acc
       else massPtsInBox0 mpts (idx+1) stop llx lly rux ruy acc

-- massPtsInBox :: [MassPoint] -> [MassPoint]
massPtsInBox :: [(Float, Float, Float)] -> Float -> Float -> Float -> Float -> [(Float, Float, Float)]
massPtsInBox mpts llx lly rux ruy =
  let acc :: [(Float, Float, Float)]
      acc = vempty
      len = vlength mpts
  in massPtsInBox0 mpts 0 len llx lly rux ruy acc


min :: Float -> Float -> Float
min x y = if x .<. y then x else y

max :: Float -> Float -> Float
max x y = if x .>. y then x else y

minX :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Float -> Float
minX ls idx stop acc =
  if idx == stop
  then acc
  else
    let pt = vnth idx ls
        x  = pt !!! 0
    in minX ls (idx+1) stop (min x acc)

maxX :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Float -> Float
maxX ls idx stop acc =
  if idx == stop
  then acc
  else
    let pt = vnth idx ls
        x  = pt !!! 0
    in maxX ls (idx+1) stop (max x acc)


minY :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Float -> Float
minY ls idx stop acc =
  if idx == stop
  then acc
  else
    let pt = vnth idx ls
        y  = pt !!! 1
    in minY ls (idx+1) stop (min y acc)

maxY :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Float -> Float
maxY ls idx stop acc =
  if idx == stop
  then acc
  else
    let pt = vnth idx ls
        y  = pt !!! 1
    in maxY ls (idx+1) stop (max y acc)

maxAccel :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Float -> Float
maxAccel ls idx stop acc =
  if idx == stop
  then acc
  else
    let pt = vnth idx ls
        ax  = pt !!! 3
        ay  = pt !!! 4
        -- ay  = pt !!! 4
    in maxAccel ls (idx+1) stop (max (max ax ay) acc)

--------------------------------------------------------------------------------
-- Various for loops


particlesToMassPoints :: [(Float, Float, Float, Float, Float)] -> [(Float, Float, Float)]
particlesToMassPoints particles =
  let len = vlength particles
      acc :: [(Float, Float, Float)]
      acc = vempty
  in particlesToMassPoints0 particles 0 len acc

particlesToMassPoints0 :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> [(Float, Float, Float)] -> [(Float, Float, Float)]
particlesToMassPoints0 particles idx stop acc =
  if idx == stop
  then acc
  else
    let pt    = vnth idx particles
        mspt  = (pt !!! 0, pt !!! 1, pt !!! 2)
        _     = inplacevsnoc acc mspt
    in particlesToMassPoints0 particles (idx+1) stop acc

mapCalcAccel :: [(Float, Float, Float)] -> BH_Tree -> [(Float, Float)]
mapCalcAccel mpts tr =
  let len = vlength mpts
      acc :: [(Float, Float)]
      acc = vempty
  in mapCalcAccel0 mpts tr 0 len acc

mapCalcAccel0 :: [(Float, Float, Float)] -> BH_Tree -> Int -> Int -> [(Float, Float)] -> [(Float, Float)]
mapCalcAccel0 mpts tr idx stop acc =
  if idx == stop
  then acc
  else
    let mpt = vnth idx mpts
        accel = calcAccel mpt tr
        _  = inplacevsnoc acc accel
    in mapCalcAccel0 mpts tr (idx+1) stop acc

mapApplyAccel :: [(Float, Float, Float, Float, Float)] -> [(Float, Float)]-> [(Float, Float, Float, Float, Float)]
mapApplyAccel particles accels =
  let len = vlength particles
      acc :: [(Float, Float, Float, Float, Float)]
      acc = vempty
  in mapApplyAccel0 particles accels 0 len acc

mapApplyAccel0 :: [(Float, Float, Float, Float, Float)] -> [(Float, Float)] -> Int -> Int -> [(Float, Float, Float, Float, Float)] -> [(Float, Float, Float, Float, Float)]
mapApplyAccel0 particles accels idx stop acc =
  if idx == stop
  then acc
  else
    let p     = vnth idx particles
        accel = vnth idx accels
        p1    = applyAccel p accel
        _  = inplacevsnoc acc p1
    in mapApplyAccel0 particles accels (idx+1) stop acc


twoDPtsToParticles :: [(Float, Float)] -> [(Float, Float, Float, Float, Float)]
twoDPtsToParticles pts =
  let len = vlength pts
      acc :: [(Float, Float, Float, Float, Float)]
      acc = vempty
  in twoDPtsToParticles0 pts 0 len acc

twoDPtsToParticles0 :: [(Float, Float)] -> Int -> Int -> [(Float, Float, Float, Float, Float)] -> [(Float, Float, Float, Float, Float)]
twoDPtsToParticles0 pts idx stop acc =
  if idx == stop
  then acc
  else
    let pt        = vnth idx pts
        particle  = (pt !!! 0, pt !!! 1, 1.0, 0.0, 0.0)
        _     = inplacevsnoc acc particle
    in twoDPtsToParticles0 pts (idx+1) stop acc

-- Things that we want to keep out of the timing loop
oneStepPre :: [(Float, Float, Float, Float, Float)]
           -> (Float, Float, Float, Float, [(Float, Float, Float)])
oneStepPre particles =
  let len = vlength particles in
  if len == 0
  then (0.0, 0.0, 0.0, 0.0, vempty)
  else
    let pt  = vnth 0 particles
        x   = pt !!! 0
        y   = pt !!! 1
        m   = pt !!! 2
        llx = minX particles 0 len x
        lly = minY particles 0 len y
        rux = maxX particles 0 len x
        ruy = maxY particles 0 len y
        mpts = particlesToMassPoints particles
    in (llx, lly, rux, ruy, mpts)

--------------------------------------------------------------------------------

-- | Sampled RMS error calculation from PBBS
check :: [(Float, Float, Float, Float, Float)] -> Float
check particles =
  let -- global constant
      nCheck = 10.0
      err = check0 particles 0 (floatToInt nCheck) 0.0
  in err ./. nCheck

check0 :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Float -> Float
check0 particles idx stop err =
  if idx == stop
  then err
  else
    let len = vlength particles

        r       = rand
        idx_i   = (mod r (idx+1))
        p1      = vnth idx_i particles
        tup     = check00 particles idx_i 0 len 0.0 0.0
        force_x = tup !!! 0
        force_y = tup !!! 1
        force_length = sqrt ((force_x .*. force_x) .+. (force_y .*. force_y))

        diff_x = force_x .-. (p1 !!! 3)
        diff_y = force_y .-. (p1 !!! 4)
        diff_length = sqrt ((diff_x .*. diff_x) .+. (diff_y .*. diff_y))

        err_iter = force_length ./. diff_length
        err1 = err .+. err_iter
    in check0 particles (idx+1) stop err1

check00 :: [(Float, Float, Float, Float, Float)] -> Int -> Int -> Int -> Float -> Float -> (Float, Float)
check00 particles idx idx_j stop force_x force_y =
  if idx_j == stop
  then (force_x, force_y)
  else if idx == idx_j
  then check00 particles idx (idx_j+1) stop force_x force_y
  else
    let -- global constant
        gGrav = 1.0
        pt1 = vnth idx_j particles
        pt2 = vnth idx particles

        v_x = (pt1 !!! 0) .-. (pt2 !!! 0)
        v_y = (pt1 !!! 1) .-. (pt2 !!! 1)
        v_length = sqrt ((v_x .*. v_x) .+. (v_y .*. v_y))

        multiplier = (pt1 !!! 2) .*. (pt2 !!! 2) .*. gGrav ./. (v_length .*. v_length .*. v_length)

        v_x1 = v_x .*. multiplier
        v_y1 = v_y .*. multiplier

        force_x1 = force_x .+. v_x1
        force_y1 = force_x .+. v_y1
    in check00 particles idx (idx_j+1) stop force_x1 force_y1

--------------------------------------------------------------------------------

buildTree :: Float -> Float -> Float -> Float -> [(Float, Float, Float)] -> BH_Tree
buildTree llx lly rux ruy mpts =
  let len = vlength mpts in
  if len == 0
  then BH_Empty
  else if len == 1
  then
    let tup = calcCentroid mpts
    in BH_Leaf (tup !!! 0) (tup !!! 1) (tup !!! 2)
  else
    let tup  = calcCentroid mpts
        x    = tup !!! 0
        y    = tup !!! 1
        m    = tup !!! 2
        midx = (llx .+. rux) ./. 2.0
        midy = (lly .+. ruy) ./. 2.0

        p1   = massPtsInBox mpts llx lly midx midy
        tr1  = buildTree llx lly midx midy p1

        p2   = massPtsInBox mpts llx midy midx ruy
        tr2  = buildTree llx midy midx ruy p2

        p3   = massPtsInBox mpts midx midy rux ruy
        tr3  = buildTree midx midy rux ruy p3

        p4   = massPtsInBox mpts midx lly rux midy
        tr4  = buildTree midx lly rux midy p4
    in BH_Node x y m tr1 tr2 tr3 tr4

-- oneStep :: [Particle] -> [Particle]
oneStep :: [(Float, Float, Float, Float, Float)] -> Float -> Float -> Float -> Float -> [(Float, Float, Float)] -> [(Float, Float, Float, Float, Float)]
oneStep particles llx lly rux ruy mpts =
  let tr = buildTree llx lly rux ruy mpts
      -- Both of these are parallel for loops in PBBS
      accels     = mapCalcAccel mpts tr
      particles1 = mapApplyAccel particles accels
  in particles1

gibbon_main =
  let pts :: [(Float,Float)]
      pts = readArrayFile ()
      particles  = twoDPtsToParticles pts
      tup  = oneStepPre particles
      llx  = tup !!! 0
      lly  = tup !!! 1
      rux  = tup !!! 2
      ruy  = tup !!! 3
      mpts = tup !!! 4
      particles1 = iterate (oneStep particles llx lly rux ruy mpts)
  in check particles1
      -- maxAccel particles1 0 (vlength particles1) 0.0
