data Octree
  = Cell Int  -- mass
         Int  -- charge
         Int  -- flags
         Int  -- bounding radius
         Int  -- energy
         Octree Octree Octree Octree
         Octree Octree Octree Octree
  | Particle Int  -- mass
             Int  -- velocity
             Int  -- energy
  | EmptyOct

{-# ANN type Octree "Factored" #-}


buildOctree :: Int -> Octree
buildOctree d =
  if d == 0
  then Particle d (d+1) (d+2)
  else Cell d (d+3) (mod d 2) (d*10) (d*5)
       (buildOctree (d-1)) (buildOctree (d-1))
       (buildOctree (d-1)) (buildOctree (d-1))
       (buildOctree (d-1)) (buildOctree (d-1))
       (buildOctree (d-1)) (buildOctree (d-1))


-- Reduction 1: Total mass
-- Used in center-of-mass computation
-- Reads ONLY mass
sumMass :: Octree -> Int
sumMass t =
  case t of
    Cell m _ _ _ _ a b c d e f g h ->
      m + sumMass a + sumMass b + sumMass c + sumMass d
        + sumMass e + sumMass f + sumMass g + sumMass h
    Particle m _ _ ->
      m
    EmptyOct ->
      0

-- Reduction 2: Total energy
-- Physics diagnostic / stability checks
-- Reads ONLY energy
sumEnergy :: Octree -> Int
sumEnergy t =
  case t of
    Cell _ _ _ _ en a b c d e f g h ->
      en + sumEnergy a + sumEnergy b + sumEnergy c + sumEnergy d
         + sumEnergy e + sumEnergy f + sumEnergy g + sumEnergy h
    Particle _ _ en ->
      en
    EmptyOct ->
      0

-- Reduction 3: Count active cells
-- Used for adaptive refinement
-- Reads ONLY flags
countActive :: Octree -> Int -> Int
countActive t flag =
  case t of
    Cell _ _ fl _ _ a b c d e f g h ->
      let here = if fl == flag then 1 else 0
      in here + countActive a flag + countActive b flag
              + countActive c flag + countActive d flag
              + countActive e flag + countActive f flag
              + countActive g flag + countActive h flag
    Particle _ _ _ ->
      0
    EmptyOct ->
      0


-- Reduction 4: Count particles
-- Used for load balancing
countParticles :: Octree -> Int
countParticles t =
  case t of
    Particle _ _ _ ->
      1
    Cell _ _ _ _ _ a b c d e f g h ->
      countParticles a + countParticles b
      + countParticles c + countParticles d
      + countParticles e + countParticles f
      + countParticles g + countParticles h
    EmptyOct ->
      0

-- Map 1: Scale energy
-- Time-step update
-- Updates ONLY energy
scaleEnergy :: Octree -> Int -> Octree
scaleEnergy t k =
  case t of
    Cell m c f r en a b c1 d e f1 g h ->
      Cell m c f r (en * k)
           (scaleEnergy a k) (scaleEnergy b k)
           (scaleEnergy c1 k) (scaleEnergy d k)
           (scaleEnergy e k) (scaleEnergy f1 k)
           (scaleEnergy g k) (scaleEnergy h k)
    Particle m v en ->
      Particle m v (en * k)
    EmptyOct ->
      EmptyOct

-- Map 2: Clear flags
-- Reset after simulation step
clearFlags :: Octree -> Octree
clearFlags t =
  case t of
    Cell m c _ r en a b c1 d e f g h ->
      Cell m c 0 r en
           (clearFlags a) (clearFlags b)
           (clearFlags c1) (clearFlags d)
           (clearFlags e) (clearFlags f)
           (clearFlags g) (clearFlags h)
    Particle m v en ->
      Particle m v en
    EmptyOct ->
      EmptyOct

gibbon_main =
            let _ = printsym (quote "Running program OctTree Physics Simulation: ")
                _ = printsym (quote "NEWLINE")
                octTree = buildOctree 7
                _ = printsym (quote "Running pass sumMass (fold): ")
                _ = printsym (quote "NEWLINE")
                totMass = iterate (sumMass octTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sumEnergy (fold): ")
                _ = printsym (quote "NEWLINE")
                totEnergy = iterate (sumEnergy octTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countActive (fold): ")
                _ = printsym (quote "NEWLINE")
                totActive = iterate (countActive octTree 1)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countParticles (fold): ")
                _ = printsym (quote "NEWLINE")
                totParticles = iterate (countParticles octTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass scaleEnergy (map): ")
                _ = printsym (quote "NEWLINE")
                octTree' = iterate (scaleEnergy octTree 10)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass clearFlags (map): ")
                _ = printsym (quote "NEWLINE")
                octTree'' = iterate (clearFlags octTree)
                _  = printsym (quote "End")
                _  = printsym (quote "NEWLINE")
            in (totMass, totEnergy, totActive, totParticles)



