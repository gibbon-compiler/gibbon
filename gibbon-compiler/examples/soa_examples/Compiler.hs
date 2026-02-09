data IR
  = Instr Int   -- opcode
          Int   -- src1
          Int   -- src2
          Int   -- dst
          Int   -- cost
          IR
  | End



-- Cost modeling pass
-- Reads ONLY cost field
totalCost :: IR -> Int
totalCost ir =
  case ir of
    Instr _ _ _ _ cost rest ->
      cost + totalCost rest
    End ->
      0


-- Instruction mix statistics
-- Reads ONLY opcode
countLoads :: IR -> Int
countLoads ir =
  case ir of
    Instr op _ _ _ _ rest ->
      let here = if (op == 1) then 1 else 0
      in here + countLoads rest
    End ->
      0

-- Register pressure estimation
-- Reads ONLY destination field
countWrites :: IR -> Int
countWrites ir =
  case ir of
    Instr _ _ _ dst _ rest ->
      let here = if (dst >= 0) then 1 else 0
      in here + countWrites rest
    End ->
      0

-- Operand usage statistics
-- Reads ONLY src fields
sumOperands :: IR -> Int
sumOperands ir =
  case ir of
    Instr _ s1 s2 _ _ rest ->
      s1 + s2 + sumOperands rest
    End ->
      0

-- Pipeline / scheduling simulation
-- Updates ONLY cost field
bumpCost :: IR -> Int -> IR
bumpCost ir k =
  case ir of
    Instr op s1 s2 dst cost rest ->
      Instr op s1 s2 dst (cost + k)
            (bumpCost rest k)
    End ->
      End

-- Dead code cleanup preparation
-- Zeroes operands only
clearOperands :: IR -> IR
clearOperands ir =
  case ir of
    Instr op _ _ dst cost rest ->
      Instr op 0 0 dst cost
            (clearOperands rest)
    End ->
      End





