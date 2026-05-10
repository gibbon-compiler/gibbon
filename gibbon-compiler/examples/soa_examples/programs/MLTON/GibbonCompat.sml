structure GibbonCompat = struct
  val itersRef = ref 1
  val sizeParamRef = ref 0

  infix 7 div mod

  (* Match C/Gibbon semantics: trunc toward zero, remainder with sign of dividend. *)
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
        val w = Word64.+ (Word64.* (ws, 0w1103 : Word64.word),
                          Word64.+ (Word64.* (Word64.fromInt salt, 0w97 : Word64.word), 0w13 : Word64.word))
        (* Convert to 32-bit, which naturally wraps on overflow *)
        val w32 = Word32.fromLarge (Word64.toLarge w)
        (* Interpret as signed 32-bit int *)
      in
        Word32.toIntX w32
      end

  fun rand x =
      absI (mixSeed x (!sizeParamRef))

  fun showBool b = if b then "#t" else "#f"

  fun quote s = s

  fun printsym s =
      if s = "NEWLINE" then
        (print "\n"; ())
      else
        (print s; ())

  fun parseIters args =
      case args of
          "--iterate" :: n :: _ =>
            (case Int.fromString n of SOME v => v | NONE => 1)
        | _ => 1

  fun parseSizeParam args =
      case args of
          "--size-param" :: n :: _ =>
            (case Int.fromString n of SOME v => v | NONE => 0)
        | "--salt" :: n :: _ =>
            (case Int.fromString n of SOME v => v | NONE => 0)
        | _ => 0

  fun setIters n = (itersRef := n)
  fun setSizeParam n = (sizeParamRef := n)
  fun getSizeParam () = !sizeParamRef

  fun printIterTimes times =
      let
        fun fmt t = Real.fmt (StringCvt.FIX (SOME 6)) t
        fun loop [] = ()
          | loop [x] = (print (fmt x); print "]\n")
          | loop (x::xs) = (print (fmt x); print ", "; loop xs)
      in
        print "ITER TIMES: [";
        loop times
      end

  fun iterate thunk =
      let
        val iters = !itersRef
        fun loop 0 acc lastOpt =
            (printIterTimes (rev acc);
             case lastOpt of SOME v => v | NONE => thunk ())
          | loop n acc _ =
            let
              val t0 = Time.now ()
              val v = thunk ()
              val t1 = Time.now ()
              val dt = Time.toReal (Time.- (t1, t0))
            in
              loop (n - 1) (dt :: acc) (SOME v)
            end
      in
        if iters <= 0 then thunk () else loop iters [] NONE
      end

  fun runGibbonMain f =
      let
        val args = CommandLine.arguments ()
        val iters = parseIters args
        val sz = parseSizeParam args
        val _ = setIters iters
        val _ = setSizeParam sz
        val _ = f ()
      in
        ()
      end
end
