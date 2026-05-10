open Real.Math

structure GibbonCompat = struct
  val sizeParamRef = ref 0

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

  infix 7 div mod
  fun op div (a:int, b:int) = Int.quot (a, b)
  fun op mod (a:int, b:int) = Int.rem (a, b)
end

open GibbonCompat

fun test_absI () =
  let
    val x = 17
    val result = absI x
    val _ = print ("absI(17) = " ^ Int.toString(result) ^ "\n")
    val y = ~5
    val result2 = absI y
    val _ = print ("absI(-5) = " ^ Int.toString(result2) ^ "\n")
  in
    ()
  end

fun test_mixSeed () =
  let
    val s = 17
    val salt = 3
    val result = mixSeed s salt
    val _ = print ("mixSeed(17, 3) = " ^ Int.toString(result) ^ "\n")
  in
    ()
  end

fun test_multiplication () =
  let
    val a = 19699
    val b = 15449
    val result = a * b
    val _ = print ("19699 * 15449 = " ^ Int.toString(result) ^ "\n")
  in
    ()
  end

val _ =
  (test_absI ();
   test_mixSeed ();
   test_multiplication ())
