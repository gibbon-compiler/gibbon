val () = let
  val a = Word.fromInt 268435456  (* 2^28 *)
  val b = Word.fromInt 268435456
  val product = Word.* (a, b)  (* should overflow *)
  val result = Word.toInt product
  val _ = print ("a = " ^ Word.toString(a) ^ "\n")
  val _ = print ("b = " ^ Word.toString(b) ^ "\n")
  val _ = print ("product = " ^ Word.toString(product) ^ "\n")
  val _ = print ("result as Int = " ^ Int.toString(result) ^ "\n")
in
  ()
end
