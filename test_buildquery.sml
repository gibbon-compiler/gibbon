structure GibbonCompat = struct
  val sizeParamRef = ref 0

  infix 7 div mod
  fun op div (a:int, b:int) = Int.quot (a, b)
  fun op mod (a:int, b:int) = Int.rem (a, b)

  fun absI x =
      if x < 0 then
        let
          val wx = Word64.fromInt x
          val w = Word64.- (0w0, wx)
        in
          Word64.toIntX w
        end
      else x

  fun mixSeed s salt =
      let
        val ws = Word64.fromInt s
        val w = Word64.+ (Word64.* (ws, 0w1103),
                          Word64.+ (Word64.* (Word64.fromInt salt, 0w97), 0w13))
      in
        Word64.toIntX w
      end

  fun maxI (a, b) = if a > b then a else b
end

open GibbonCompat

datatype Query = Join of int * int * int * int * Query * Query
               | Filter of int * int * int * int * Query
               | Scan of int * int * int * int
               | QEmpty

fun buildQuery (d, seed) =
  let
    val _ = print ("Building Query at depth " ^ Int.toString(d) ^ "\n")
  in
  if d = 0
  then
    let
      val tableId = (absI seed) mod 17
      val rows = 2000 + (absI (mixSeed seed 3)) mod 6000
      val cost = 20 + rows div 16
      val width = 24 + (absI (mixSeed seed 7)) mod 120
      val _ = print ("Scan: tableId=" ^ Int.toString(tableId) ^ " rows=" ^ Int.toString(rows) ^ "\n")
    in Scan (tableId, rows, cost, width)
    end
  else
    let
      val _ = print ("Computing tag at depth " ^ Int.toString(d) ^ ", seed=" ^ Int.toString(seed) ^ "\n")
      val mixSeedResult = mixSeed seed 11
      val _ = print ("mixSeed(seed, 11) = " ^ Int.toString(mixSeedResult) ^ "\n")
      val absResult = absI(mixSeedResult)
      val _ = print ("absI(...) = " ^ Int.toString(absResult) ^ "\n")
      val tag = absResult mod 4
      val _ = print ("tag = " ^ Int.toString(tag) ^ "\n")
    in
    if tag < 2
    then
      let
        val _ = print ("Building Join at depth " ^ Int.toString(d) ^ "\n")
        val l = buildQuery (d - 1, mixSeed seed 1)
        val rDepth = if d > 1 then d - 2 else 0
        val _ = print ("About to build right subtree at depth " ^ Int.toString(rDepth) ^ "\n")
        val r = buildQuery (rDepth, mixSeed seed 2)
        val _ = print ("Building Join stage 2 at depth " ^ Int.toString(d) ^ "\n")
        val joinTy = (absI (mixSeed seed 13)) mod 3
        val _ = print ("Computing lRows and rRows\n")
        val lRows = 1200 + d * 220 + (absI (mixSeed seed 17)) mod 2000
        val _ = print ("lRows=" ^ Int.toString(lRows) ^ "\n")
        val rRows = 1000 + d * 170 + (absI (mixSeed seed 19)) mod 1700
        val _ = print ("rRows=" ^ Int.toString(rRows) ^ "\n")
        val sel = 60 + (absI (mixSeed seed 23)) mod 260
        val _ = print ("sel=" ^ Int.toString(sel) ^ "\n")
        val _ = print ("About to compute lRows * rRows\n")
        val product = lRows * rRows
        val _ = print ("lRows * rRows = " ^ Int.toString(product) ^ "\n")
        val divisor = sel * 10 + 1
        val _ = print ("divisor=" ^ Int.toString(divisor) ^ "\n")
        val outRows = maxI(1, product div divisor)
        val joinCpu =
          if joinTy = 0
          then (lRows * rRows) div 2400
          else if joinTy = 1
               then (lRows + rRows) div 7
               else (lRows + rRows) div 9
        val total = 30 + joinCpu + outRows div 20
        val mem = if joinTy = 1 then (rRows div 2) else (outRows div 8)
        val _ = print ("Join: lRows=" ^ Int.toString(lRows) ^ " rRows=" ^ Int.toString(rRows) ^
                       " outRows=" ^ Int.toString(outRows) ^ "\n")
      in Join (joinTy, outRows, total, mem, l, r)
      end
    else
      let
        val _ = print ("Building Filter at depth " ^ Int.toString(d) ^ "\n")
        val s = buildQuery (d - 1, mixSeed seed 3)
        val predId = (absI (mixSeed seed 29)) mod 31
        val sel = 120 + (absI (mixSeed seed 31)) mod 760
        val cpu = 4 + (absI (mixSeed seed 37)) mod 40
        val flags = (absI (mixSeed seed 41)) mod 8
      in Filter (predId, sel, cpu, flags, s)
      end
    end
  end

val _ = buildQuery (3, 17)
val _ = print "Success!\n"
