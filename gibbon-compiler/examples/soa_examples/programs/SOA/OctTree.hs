-- @BENCH adt_fields=16
data Octree
  = Cell Int  -- aggregate mass of the cell
         Int  -- center-of-mass position (1D proxy)
         Int  -- number of contained particles
         Int  -- half-size of the cell
         Int  -- aggregate momentum
         Octree Octree Octree Octree
         Octree Octree Octree Octree
  | Particle Int  -- mass
             Int  -- position
             Int  -- velocity
  | EmptyOct

{-# ANN type Octree "Factored" #-}

absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

maxI :: Int -> Int -> Int
maxI a b = if a > b then a else b

sum8 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
sum8 a b c d e f g h = a + b + c + d + e + f + g + h

mixSeed :: Int -> Int -> Int
mixSeed s salt = s * 1103 + salt * 97 + 13

massOf :: Octree -> Int
massOf t =
  case t of
    Cell m _ _ _ _ _ _ _ _ _ _ _ _ ->
      m
    Particle m _ _ ->
      m
    EmptyOct ->
      0

weightedPos :: Octree -> Int
weightedPos t =
  case t of
    Cell m c _ _ _ _ _ _ _ _ _ _ _ ->
      m * c
    Particle m p _ ->
      m * p
    EmptyOct ->
      0

countOf :: Octree -> Int
countOf t =
  case t of
    Cell _ _ n _ _ _ _ _ _ _ _ _ _ ->
      n
    Particle _ _ _ ->
      1
    EmptyOct ->
      0

momentumOf :: Octree -> Int
momentumOf t =
  case t of
    Cell _ _ _ _ mom _ _ _ _ _ _ _ _ ->
      mom
    Particle m _ v ->
      m * v
    EmptyOct ->
      0

-- Build a hierarchical octree with pseudo-randomized particles and cached aggregates.
{-# ANN buildOctree "OPT:StoreScalarCounts" #-}
buildOctree :: Int -> Int -> Int -> Int -> Octree
buildOctree d seed center half =
  if d == 0
  then
    let m = 1 + mod (absI seed) 5
        p = center + mod (mixSeed seed 3) 3 - 1
        v = mod (mixSeed seed 11) 11 - 5
    in Particle m p v
  else
    let half' = maxI 1 (half / 2)
        stride = maxI 1 (half / 4)
        o0 = 0 - (stride * 7)
        o1 = 0 - (stride * 5)
        o2 = 0 - (stride * 3)
        o3 = 0 - stride
        o4 = stride
        o5 = stride * 3
        o6 = stride * 5
        o7 = stride * 7
        c0 = buildOctree (d - 1) (mixSeed seed 1) (center + o0) half'
        c1 = buildOctree (d - 1) (mixSeed seed 2) (center + o1) half'
        c2 = buildOctree (d - 1) (mixSeed seed 3) (center + o2) half'
        c3 = buildOctree (d - 1) (mixSeed seed 4) (center + o3) half'
        c4 = buildOctree (d - 1) (mixSeed seed 5) (center + o4) half'
        c5 = buildOctree (d - 1) (mixSeed seed 6) (center + o5) half'
        c6 = buildOctree (d - 1) (mixSeed seed 7) (center + o6) half'
        c7 = buildOctree (d - 1) (mixSeed seed 8) (center + o7) half'
        m0 = massOf c0
        m1 = massOf c1
        m2 = massOf c2
        m3 = massOf c3
        m4 = massOf c4
        m5 = massOf c5
        m6 = massOf c6
        m7 = massOf c7
        mTot = sum8 m0 m1 m2 m3 m4 m5 m6 m7
        wTot = sum8 (weightedPos c0) (weightedPos c1) (weightedPos c2) (weightedPos c3)
                    (weightedPos c4) (weightedPos c5) (weightedPos c6) (weightedPos c7)
        nTot = sum8 (countOf c0) (countOf c1) (countOf c2) (countOf c3)
                    (countOf c4) (countOf c5) (countOf c6) (countOf c7)
        pTot = sum8 (momentumOf c0) (momentumOf c1) (momentumOf c2) (momentumOf c3)
                    (momentumOf c4) (momentumOf c5) (momentumOf c6) (momentumOf c7)
        com = if mTot == 0 then center else wTot / mTot
    in Cell mTot com nTot half pTot c0 c1 c2 c3 c4 c5 c6 c7

-- Reduction 1: total mass.
sumMass :: Octree -> Int
sumMass t =
  case t of
    Cell _ _ _ _ _ a b c d e f g h ->
      sum8
        (sumMass a) (sumMass b) (sumMass c) (sumMass d)
        (sumMass e) (sumMass f) (sumMass g) (sumMass h)
    Particle m _ _ ->
      m
    EmptyOct ->
      0

-- Reduction 2: kinetic energy plus coarse potential using cached cell aggregates.
sumEnergy :: Octree -> Int
sumEnergy t =
  case t of
    Cell m c _ s mom a b c1 d e f g h ->
      let dist = absI c + 1
          bulk = (m * mom * mom) / (m * m + 1)
          pot = (m * s * 50) / dist
      in bulk + pot + sum8
                      (sumEnergy a) (sumEnergy b) (sumEnergy c1) (sumEnergy d)
                      (sumEnergy e) (sumEnergy f) (sumEnergy g) (sumEnergy h)
    Particle m _ v ->
      (m * v * v) / 2
    EmptyOct ->
      0

-- Reduction 3: count cells that fail Barnes-Hut opening criterion and need refinement.
countActive :: Octree -> Int -> Int
countActive t theta =
  case t of
    Cell _ c _ s _ a b c1 d e f g h ->
      let probe = 0
          dist = absI (c - probe) + 1
          openLhs = s * 100
          openRhs = theta * dist
          refine = if openLhs >= openRhs then 1 else 0
      in refine + sum8
                    (countActive a theta) (countActive b theta) (countActive c1 theta) (countActive d theta)
                    (countActive e theta) (countActive f theta) (countActive g theta) (countActive h theta)
    Particle _ _ _ ->
      0
    EmptyOct ->
      0

-- Reduction 4: particle count.
countParticles :: Octree -> Int
countParticles t =
  case t of
    Particle _ _ _ ->
      1
    Cell _ _ _ _ _ a b c d e f g h ->
      sum8
        (countParticles a) (countParticles b) (countParticles c) (countParticles d)
        (countParticles e) (countParticles f) (countParticles g) (countParticles h)
    EmptyOct ->
      0

-- Barnes-Hut pass: uses cell aggregate when far, descends when near.
barnesHutPotential :: Octree -> Int -> Int -> Int
barnesHutPotential t probe theta =
  case t of
    Cell m c n s _ a b c1 d e f g h ->
      let dist = absI (c - probe) + 1
          openLhs = s * 100
          openRhs = theta * dist
          approx = if n == 0 then 0 else (m * 1000) / (dist * dist)
          recur = sum8
                    (barnesHutPotential a probe theta)
                    (barnesHutPotential b probe theta)
                    (barnesHutPotential c1 probe theta)
                    (barnesHutPotential d probe theta)
                    (barnesHutPotential e probe theta)
                    (barnesHutPotential f probe theta)
                    (barnesHutPotential g probe theta)
                    (barnesHutPotential h probe theta)
      in if openLhs < openRhs then approx else recur
    Particle m p _ ->
      let dist = absI (p - probe) + 1
      in (m * 1000) / (dist * dist)
    EmptyOct ->
      0

-- Upward multipole truncation using only mass and dipole proxy.
fmmUpSeries :: Int -> Int -> Int -> Int
fmmUpSeries m dip order =
  if order <= 0
  then m * 100
  else
    let prev = fmmUpSeries m dip (order - 1)
        corr = absI dip / (order * 20 + 1)
    in prev + corr

-- Downward/local evaluation truncation using cell size and momentum proxy.
fmmDownSeries :: Int -> Int -> Int -> Int -> Int -> Int
fmmDownSeries m mom s dist order =
  if order <= 0
  then (m * 100) / dist
  else
    let prev = fmmDownSeries m mom s dist (order - 1)
        d = dist + order
        corr = ((absI mom) + s * order) / (d * d + 1)
    in prev + corr

-- Single-pass FMM approximation:
-- combines upward-style multipole accumulation with downward-style far/near evaluation.
fmmPotential :: Octree -> Int -> Int -> Int -> Int
fmmPotential t probe order eta =
  case t of
    Cell m c _ s mom a b c1 d e f g h ->
      let dist = absI (c - probe) + 1
          farLhs = s * 100
          farRhs = eta * dist
          upMoment = fmmUpSeries m (m * c) order
          downApprox = fmmDownSeries m mom s dist order
          approx = (upMoment / (dist + 1)) + downApprox
          recur = sum8
                    (fmmPotential a probe order eta)
                    (fmmPotential b probe order eta)
                    (fmmPotential c1 probe order eta)
                    (fmmPotential d probe order eta)
                    (fmmPotential e probe order eta)
                    (fmmPotential f probe order eta)
                    (fmmPotential g probe order eta)
                    (fmmPotential h probe order eta)
      in if farLhs < farRhs then approx else recur
    Particle m p v ->
      let dist = absI (p - probe) + 1
          up = fmmUpSeries m (m * p) order
      in (up / (dist + 1)) + ((m * 100) + absI v) / dist
    EmptyOct ->
      0

-- Map 1: damp momentum and scale velocities (models global timestep update).
{-# ANN scaleEnergy "OPT:CanVectorize" #-}
scaleEnergy :: Octree -> Int -> Octree
scaleEnergy t k =
  case t of
    Cell m c n s mom a b c1 d e f g h ->
      let mom' = (mom * k) / (s + 1)
      in Cell m c n s mom'
           (scaleEnergy a k) (scaleEnergy b k) (scaleEnergy c1 k) (scaleEnergy d k)
           (scaleEnergy e k) (scaleEnergy f k) (scaleEnergy g k) (scaleEnergy h k)
    Particle m p v ->
      let v' = (v * k) / 10
      in Particle m p v'
    EmptyOct ->
      EmptyOct

-- Map 2: clear per-node particle-count cache for a fresh accumulation phase.
{-# ANN clearFlags "OPT:CanVectorize" #-}
clearFlags :: Octree -> Octree
clearFlags t =
  case t of
    Cell m c _ s mom a b c1 d e f g h ->
      Cell m c 0 s mom
           (clearFlags a) (clearFlags b) (clearFlags c1) (clearFlags d)
           (clearFlags e) (clearFlags f) (clearFlags g) (clearFlags h)
    Particle m p v ->
      Particle m p v
    EmptyOct ->
      EmptyOct

gibbon_main =
            let _ = printsym (quote "Running program OctTree Physics Simulation: ")
                _ = printsym (quote "NEWLINE")
                octTree = buildOctree (sizeParam + 7) 17 0 64

                _ = printsym (quote "Running pass sumMass (fold, uses=10): ")
                _ = printsym (quote "NEWLINE")
                totMass = iterate (sumMass octTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sumEnergy (fold, uses=12): ")
                _ = printsym (quote "NEWLINE")
                totEnergy = iterate (sumEnergy octTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countActive (fold, uses=10): ")
                _ = printsym (quote "NEWLINE")
                totActive = iterate (countActive octTree 60)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countParticles (fold, uses=8): ")
                _ = printsym (quote "NEWLINE")
                totParticles = iterate (countParticles octTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass barnesHutPotential (fold_like, uses=11): ")
                _ = printsym (quote "NEWLINE")
                bhPotential = iterate (barnesHutPotential octTree 21 60)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass fmmPotential (fold_like, uses=12): ")
                _ = printsym (quote "NEWLINE")
                fmmPot = iterate (fmmPotential octTree 21 4 70)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass scaleEnergy (map, uses=16): ")
                _ = printsym (quote "NEWLINE")
                octTree' = iterate (scaleEnergy octTree 9)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass clearFlags (map, uses=15): ")
                _ = printsym (quote "NEWLINE")
                octTree'' = iterate (clearFlags octTree)
                _  = printsym (quote "End")
                _  = printsym (quote "NEWLINE")
                scaledEnergy = sumEnergy octTree'
                clearedActive = countActive octTree'' 60
            in (totMass, totEnergy, totActive, totParticles, bhPotential, fmmPot, scaledEnergy, clearedActive)
