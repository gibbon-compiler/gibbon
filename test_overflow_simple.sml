structure Test = struct
  fun mixSeed_debug s salt =
      let
        val ws = Word64.fromInt s
        val mult1 = Word64.* (ws, 0w1103)
        val wsalt = Word64.fromInt salt
        val mult2 = Word64.* (wsalt, 0w97)
        val sum1 = Word64.+ (mult2, 0w13)
        val w = Word64.+ (mult1, sum1)
      in
        print ("Input: s=" ^ Int.toString(s) ^ " salt=" ^ Int.toString(salt) ^ "\n");
        print ("ws * 1103 = " ^ Word64.toString(mult1) ^ "\n");
        print ("salt * 97 = " ^ Word64.toString(mult2) ^ "\n");
        print ("Result = " ^ Word64.toString(w) ^ "\n");
        print ("Max 31-bit signed int: 1073741823\n");
        print ("The result is larger and will overflow!\n")
      end
end

open Test

val _ = mixSeed_debug 21017775 11
