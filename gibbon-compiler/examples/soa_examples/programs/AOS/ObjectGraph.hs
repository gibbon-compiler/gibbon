-- @BENCH adt_fields=5
data Heap
  = Obj Int    -- object id
        Int    -- size
        Int    -- mark bit
        Heap
        Heap
  | Null

{-# ANN type Heap "Linear" #-}


-- Builds a balanced heap tree of given depth
-- id grows with depth, size grows linearly, mark alternates
buildHeap :: Int -> Heap
buildHeap d =
  if (d == 0)
  then Null
  else
    let id   = d
        size = d * 10
        mark = d - (d / 2) * 2   -- pseudo even/odd
        l    = buildHeap (d - 1)
        r    = buildHeap (d - 1)
    in Obj id size mark l r


-- Heap memory usage estimation
-- Reads ONLY size field
totalHeapSize :: Heap -> Int
totalHeapSize h =
  case h of
    Obj _ size _ l r ->
      size + totalHeapSize l + totalHeapSize r
    Null ->
      0

-- GC marking statistics
-- Reads ONLY mark bit
countMarked :: Heap -> Int
countMarked h =
  case h of
    Obj _ _ mark l r ->
      let here = if (mark == 1) then 1 else 0
      in here + countMarked l + countMarked r
    Null ->
      0

-- Heap profiling pass
-- Used to identify large objects
-- Reads ONLY size field
countLarge :: Heap -> Int -> Int
countLarge h limit =
  case h of
    Obj _ size _ l r ->
      let here = if (size > limit) then 1 else 0
      in here + countLarge l limit + countLarge r limit
    Null ->
      0

-- GC accounting: bytes in marked objects (live set size).
liveBytes :: Heap -> Int
liveBytes h =
  case h of
    Obj _ size mark l r ->
      let here = if (mark == 1) then size else 0
      in here + liveBytes l + liveBytes r
    Null ->
      0

-- GC accounting: bytes in unmarked objects (reclaimable at sweep).
deadBytes :: Heap -> Int
deadBytes h =
  case h of
    Obj _ size mark l r ->
      let here = if (mark == 0) then size else 0
      in here + deadBytes l + deadBytes r
    Null ->
      0

-- Generational-style stat: number of marked objects below a size cutoff.
countSurvivors :: Heap -> Int -> Int
countSurvivors h maxSize =
  case h of
    Obj _ size mark l r ->
      let here =
            if (mark == 1)
            then if (size <= maxSize) then 1 else 0
            else 0
      in here + countSurvivors l maxSize + countSurvivors r maxSize
    Null ->
      0

-- Debug / profiling checksum
-- Reads ONLY object id
sumObjIds :: Heap -> Int
sumObjIds h =
  case h of
    Obj id _ _ l r ->
      id + sumObjIds l + sumObjIds r
    Null ->
      0

-- GC reset phase
-- Updates ONLY mark bit
clearMarks :: Heap -> Heap
clearMarks h =
  case h of
    Obj id size _ l r ->
      Obj id size 0
          (clearMarks l)
          (clearMarks r)
    Null ->
      Null

-- Sweep phase:
-- reclaim unmarked objects by zeroing size, and clear mark bits for next cycle.
sweepUnmarked :: Heap -> Heap
sweepUnmarked h =
  case h of
    Obj id size mark l r ->
      let size' = if (mark == 1) then size else 0
      in Obj id size' 0
             (sweepUnmarked l)
             (sweepUnmarked r)
    Null ->
      Null

-- Allocation growth simulation
-- Updates ONLY size field
inflateSizes :: Heap -> Int -> Heap
inflateSizes h k =
  case h of
    Obj id size mark l r ->
      Obj id (size + k) mark
          (inflateSizes l k)
          (inflateSizes r k)
    Null ->
      Null

-- Mutator-style update:
-- periodically "touch" hot objects, setting mark and increasing size.
touchHotObjects :: Heap -> Int -> Int -> Heap
touchHotObjects h stride delta =
  case h of
    Obj id size mark l r ->
      let hot = (mod id stride) == 0
          size' = if hot then size + delta else size
          mark' = if hot then 1 else mark
      in Obj id size' mark'
             (touchHotObjects l stride delta)
             (touchHotObjects r stride delta)
    Null ->
      Null

-- Decay pass:
-- shrink cold/unmarked objects to emulate reclamation/compaction pressure.
decayColdObjects :: Heap -> Int -> Heap
decayColdObjects h k =
  case h of
    Obj id size mark l r ->
      let reduced = size - k
          size' =
            if (mark == 0)
            then if (reduced < 0) then 0 else reduced
            else size
      in Obj id size' mark
             (decayColdObjects l k)
             (decayColdObjects r k)
    Null ->
      Null

gibbon_main =
            let _ = printsym (quote "Running program ObjectGraph Simulated a GC Program: ")
                _ = printsym (quote "NEWLINE")
                heap = buildHeap 23
                _ = printsym (quote "Running pass totalHeapSize (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                heapSize = iterate (totalHeapSize heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countMarked (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                countMarkedItems = iterate (countMarked heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countLargeItems (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                countLargeItems = iterate (countLarge heap 100)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass liveBytes (fold, uses=4): ")
                _ = printsym (quote "NEWLINE")
                liveSet = iterate (liveBytes heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass deadBytes (fold, uses=4): ")
                _ = printsym (quote "NEWLINE")
                reclaimable = iterate (deadBytes heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countSurvivors (fold, uses=4): ")
                _ = printsym (quote "NEWLINE")
                survivors = iterate (countSurvivors heap 120)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sumObjIds (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                sObjIds = iterate (sumObjIds heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sweepUnmarked (map, uses=5): ")
                _ = printsym (quote "NEWLINE")
                heapSwept = iterate (sweepUnmarked heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass touchHotObjects (map, uses=5): ")
                _ = printsym (quote "NEWLINE")
                heapHot = iterate (touchHotObjects heap 4 12)
                _  = printsym (quote "End")
                _  = printsym (quote "NEWLINE")
            in (heapSize, countMarkedItems, countLargeItems, liveSet, reclaimable, survivors, sObjIds)
