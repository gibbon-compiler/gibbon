
-- @BENCH adt_fields=5
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
            let _ = printsym (quote "Running program ObjectGraph Simulated a GC Program: ")
                _ = printsym (quote "NEWLINE")
                heap = buildHeap 20
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
                _ = printsym (quote "Running pass sumObjIds (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                sObjIds = iterate (sumObjIds heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass clearMarks (map, uses=4): ")
                _ = printsym (quote "NEWLINE")
                heap' = iterate (clearMarks heap)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass inflateSizes (map, uses=5): ")
                _ = printsym (quote "NEWLINE")
                heap'' = iterate (inflateSizes heap 10)
                _  = printsym (quote "End")
                _  = printsym (quote "NEWLINE")
            in (heapSize, countMarkedItems, countLargeItems, sObjIds)
