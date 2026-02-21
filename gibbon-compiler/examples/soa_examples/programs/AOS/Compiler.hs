-- LLVM-inspired linear IR

-- @BENCH adt_fields=9
data IR
  = Instr Int   -- opcode (see encoding below)
          Int   -- flags
          Int   -- src1
          Int   -- src2
          Int   -- dst
          Int   -- latency
          Int   -- throughput
          IR
  | BlockEnd    -- basic block terminator
          IR
  | End

{-# ANN type IR "Linear" #-}

-- Opcode encoding:
-- 0: ALU      (add, mul, fadd, etc.)
-- 1: Load     (load)
-- 2: Store    (store)
-- 3: Compare  (icmp, fcmp)
-- 4: Branch   (br, switch)
-- 5: Call     (call, invoke)
-- 6: Phi      (phi)
-- 7: Cast     (bitcast, zext, fptosi, ...)

-- buildIR :: Int -> IR
-- buildIR n =
--    if n <= 0
--    then End
--    else if mod n 7 == 0
--    then BlockEnd (buildIR (n - 1))
--    else
--     let
--        op   = mod n 8
--        flags = mod (n*3) 16
--        lat  = 1 + mod n 5
--        thr  = 1 + mod n 3
--       in Instr op flags (n-1) (n-2) n lat thr (buildIR (n - 1))

-- Build "LLVM-valid-ish" IR:
-- After every BlockEnd, emit a small fixed number of PHIs at the start of the next block.
buildIR_validPhi_go :: Int -> Int -> IR
buildIR_validPhi_go n pendingPhi =
  if n <= 0
  then End

  else if pendingPhi > 0
  then
    -- Emit PHIs at block start without consuming n
    Instr 6 0 0 0 0 1 1 (buildIR_validPhi_go n (pendingPhi - 1))

  else if mod n 7 == 0
  then
    -- New block boundary; queue PHIs for next block
    BlockEnd (buildIR_validPhi_go (n - 1) 2)

  else
    let op0   = mod n 8 in
    let op    = if op0 == 6 then 0 else op0 in   -- avoid PHI in block body
    let flags = mod (n * 3) 16 in
    let lat   = 1 + mod n 5 in
    let thr   = 1 + mod n 3 in
    Instr op flags (n-1) (n-2) n lat thr (buildIR_validPhi_go (n - 1) 0)

instCountPass :: IR -> Int
instCountPass ir =
  case ir of
    Instr _ _ _ _ _ _ _ rest ->
      1 + instCountPass rest
    BlockEnd rest ->
      instCountPass rest
    End ->
      0

blockCountPass :: IR -> Int
blockCountPass ir =
  case ir of
    BlockEnd rest ->
      1 + blockCountPass rest
    Instr _ _ _ _ _ _ _ rest ->
      blockCountPass rest
    End ->
      0

castInstCountPass :: IR -> Int
castInstCountPass ir =
  case ir of
    Instr op _ _ _ _ _ _ rest ->
      let isCast = if op == 7 then 1 else 0
      in isCast + castInstCountPass rest
    BlockEnd rest ->
      castInstCountPass rest
    End ->
      0

goHasCycle :: IR -> Int -> Bool
goHasCycle ir curBlock =
  case ir of
    Instr op _ tgt _ _ _ _ rest ->
      let isBackedge = (op == 4) && (tgt < curBlock)
          restHasCycle = goHasCycle rest curBlock
      in isBackedge || restHasCycle
    BlockEnd rest ->
      goHasCycle rest (curBlock + 1)
    End -> False

memoryOpStatsPass :: IR -> Int
memoryOpStatsPass ir =
  case ir of
    Instr _ flags _ _ _ _ _ rest ->
      let isMem = if (flags == 1 || flags == 2) then 1 else 0
      in isMem + memoryOpStatsPass rest
    BlockEnd rest ->
      memoryOpStatsPass rest
    End ->
      0

branchStatsPass :: IR -> Int
branchStatsPass ir =
  case ir of
    Instr _ flags _ _ _ _ _ rest ->
      let isBr = if flags == 4 then 1 else 0
      in isBr + branchStatsPass rest
    BlockEnd rest ->
      branchStatsPass rest
    End ->
      0

latencyModelPass :: IR -> Int
latencyModelPass ir =
  case ir of
    Instr _ _ _ _ _ lat _ rest ->
      lat + latencyModelPass rest
    BlockEnd rest ->
      latencyModelPass rest
    End ->
      0

throughputModelPass :: IR -> Int
throughputModelPass ir =
  case ir of
    Instr _ _ _ _ _ _ thr rest ->
      thr + throughputModelPass rest
    BlockEnd rest ->
      throughputModelPass rest
    End ->
      0

targetRetunePass :: IR -> Int -> IR
targetRetunePass ir k =
  case ir of
    Instr op fl s1 s2 dst lat thr rest ->
      Instr op fl s1 s2 dst (lat * k) thr
            (targetRetunePass rest k)
    BlockEnd rest ->
      BlockEnd (targetRetunePass rest k)
    End ->
      End

stripSideEffectsPass :: IR -> IR
stripSideEffectsPass ir =
  case ir of
    Instr op _ s1 s2 dst lat thr rest ->
      Instr op 0 s1 s2 dst lat thr
            (stripSideEffectsPass rest)
    BlockEnd rest ->
      BlockEnd (stripSideEffectsPass rest)
    End ->
      End

-- Verifier pass with side effects only.
-- Side effect: prints a short marker if it sees an invalid condition.
-- Realistic: LLVM verifier reports diagnostics; here we emit tiny markers.
verifyPhiPlacement_IO :: IR -> Int -> ()
verifyPhiPlacement_IO ir seenNonPhi =
  case ir of
    End ->
      ()

    BlockEnd rest ->
      -- new block: we are back in the "PHI prefix"
      verifyPhiPlacement_IO rest 0

    Instr op fl s1 s2 dst lat thr rest ->
      let _ = if op == 6
              then
                if seenNonPhi == 1
                then printsym (quote "BADPHI ")
                else ()
              else ()
          seenNonPhi' = if op == 6
                            then seenNonPhi
                            else 1
      in verifyPhiPlacement_IO rest seenNonPhi'


gibbon_main =
  let _ = printsym (quote "Running the Compiler IR Program: ")
      _ = printsym (quote "NEWLINE")
      ir     = buildIR_validPhi_go (sizeParam + 5000000) 0
      -- we can verify IR here
      _ = printsym (quote "Running pass verifyIR (fold, uses=9): ")
      _ = printsym (quote "NEWLINE")
      _  = iterate (verifyPhiPlacement_IO ir 0)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass instCountPass (fold, uses=2): ")
      _ = printsym (quote "NEWLINE")
      insts  = iterate (instCountPass ir)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass blockCountPass (fold, uses=2): ")
      _ = printsym (quote "NEWLINE")
      blocks = iterate (blockCountPass ir)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass memoryOpStatsPass (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      memops = iterate (memoryOpStatsPass ir)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass castInstCountPass (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      castInstrs = iterate (castInstCountPass ir)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass branchStatsPass (fold, uses=2): ")
      _ = printsym (quote "NEWLINE")
      brs    = iterate (branchStatsPass ir)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass latencyModelPass (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      lat    = iterate (latencyModelPass ir)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass has cycle (fold, uses=4): ")
      _ = printsym (quote "NEWLINE")
      hasCycle = iterate (goHasCycle ir 0)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass throughputModelPass (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      thr    = iterate (throughputModelPass ir)
      _ = printsym (quote "End: ")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass targetReturnPass (map, uses=9): ")
      _ = printsym (quote "NEWLINE")
      ir'    = iterate (targetRetunePass ir 2)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass stripSideEffectsPass (map, uses=7): ")
      _ = printsym (quote "NEWLINE")
      ir''   = iterate (stripSideEffectsPass ir')
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      --_      = printPacked ir''
  in (insts, blocks, memops, brs, lat, hasCycle, thr, instCountPass ir', instCountPass ir'')
