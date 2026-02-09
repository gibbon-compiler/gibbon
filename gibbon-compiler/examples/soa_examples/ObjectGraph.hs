data Heap
  = Obj Int    -- object id
        Int    -- size
        Int    -- mark bit
        Heap
        Heap
  | Null

{-# ANN type Heap "Factored" #-}


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

gibbon_main =
            let heap = buildHeap 20
                _ = printPacked heap
                heapSize = iterate (totalHeapSize heap)
                countMarkedItems = iterate (countMarked heap)
                countLargeItems = iterate (countLarge heap 100)
                sObjIds = iterate (sumObjIds heap)
                heap' = iterate (clearMarks heap)
                heap'' = iterate (inflateSizes heap 10)
                _  = printsym (quote "NEWLINE")
                _  = printsym (quote "NEWLINE")
            in (heapSize, countMarkedItems, countLargeItems, sObjIds)
