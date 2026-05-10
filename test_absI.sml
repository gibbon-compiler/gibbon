structure Test = struct
  fun absI x =
      if x < 0 then
        let
          val wx = Word64.fromInt x
          val w = Word64.- (0w0 : Word64.word, wx)
        in
          Word64.toIntX w
        end
      else x
end

open Test

val _ = absI (~21017775)
