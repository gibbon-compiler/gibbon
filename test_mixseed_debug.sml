structure GibbonCompat = struct
  infix 7 div mod
  fun op div (a:int, b:int) = Int.quot (a, b)
  fun op mod (a:int, b:int) = Int.rem (a, b)

  fun mixSeed_debug s salt =
      let
        val ws = Word64.fromInt s
        val mult1 = Word64.* (ws, 0w1103)
        val wsalt = Word64.fromInt salt
        val mult2 = Word64.* (wsalt, 0w97)
        val sum1 = Word64.+ (mult2, 0w13)
        val w = Word64.+ (mult1, sum1)
        val w_as_int64 = Word64.toLargeInt w
        val _ = print ("Word64 value: " ^ LargeInt.toString(w_as_int64) ^ "\n")
        val max_signed_int31 = LargeInt.fromInt(1073741823) (* 2^30 - 1 for 31-bit signed *)
        val min_signed_int31 = LargeInt.fromInt(~1073741824)
        val _ = print ("31-bit signed range: " ^ LargeInt.toString(min_signed_int31) ^ " to " ^ LargeInt.toString(max_signed_int31) ^ "\n")
      in
        ()
      end
end

open GibbonCompat

val _ = mixSeed_debug 21017775 11
val _ = print "Done\n"
