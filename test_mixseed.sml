structure GibbonCompat = struct
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
        val _ = print ("mixSeed called with s=" ^ Int.toString(s) ^ " salt=" ^ Int.toString(salt) ^ "\n")
        val ws = Word64.fromInt s
        val _ = print ("ws (Word64) created\n")
        val mult1 = Word64.* (ws, 0w1103)
        val _ = print ("ws * 1103 computed\n")
        val wsalt = Word64.fromInt salt
        val mult2 = Word64.* (wsalt, 0w97)
        val _ = print ("salt * 97 computed\n")
        val sum1 = Word64.+ (mult2, 0w13)
        val _ = print ("(salt * 97) + 13 computed\n")
        val w = Word64.+ (mult1, sum1)
        val _ = print ("Full sum computed in Word64\n")
        val result = Word64.toIntX w
        val _ = print ("Converted back to Int: " ^ Int.toString(result) ^ "\n")
      in
        result
      end
end

open GibbonCompat

val _ = mixSeed 21017775 11
val _ = print "Success!\n"
