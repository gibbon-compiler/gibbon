(* MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
   --tree-sweep), ported from BintreeBench (ECOOP 2017, treebench.sml) and
   aligned with tree_sweep/programs/*/MonoTree*.hs: 64-bit leaves, mkTree d 0
   gives every one of the 2^d leaves d(d+1)/2, and every subtree is built
   separately. Timed with clock_gettime through tb_now.c.

     treebench <build|add1|sum> --size-param DEPTH --iterate N *)

datatype tree = Leaf of Int64.int | Node of tree * tree

val nowNs = _import "tb_now_ns" : unit -> Int64.int;

fun mkTree (d : Int64.int, acc : Int64.int) : tree =
  if d = 0 then Leaf acc
  else Node (mkTree (d - 1, d + acc), mkTree (d - 1, d + acc))

fun add1Tree (Leaf x) = Leaf (x + 1)
  | add1Tree (Node (l, r)) = Node (add1Tree l, add1Tree r)

fun sumTree (Leaf x) = x
  | sumTree (Node (l, r)) = sumTree l + sumTree r

fun arg flag =
  let fun go (f :: v :: rest) = if f = flag then valOf (Int.fromString v) else go (v :: rest)
        | go _ = raise Fail ("missing " ^ flag)
  in go (CommandLine.arguments ()) end

(* Read each iteration, so the input is never a compile-time constant. *)
val depthRef = ref (Int64.fromInt (arg "--size-param"))
val iters = Int.max (1, arg "--iterate")
val times = Array.array (iters, 0.0)

fun timed i f =
  let val t0 = nowNs ()
      val r = f ()
      val t1 = nowNs ()
  in Array.update (times, i, Real.fromLargeInt (Int64.toLarge (t1 - t0)) / 1.0e9); r end

fun loop i f last = if i = iters then last else loop (i + 1) f (timed i f)

val pass = hd (CommandLine.arguments ())
val answer =
  case pass of
      "build" =>
        (print "Running pass buildTree (build): \n";
         sumTree (loop 0 (fn () => mkTree (!depthRef, 0)) (Leaf 0)))
    | "add1" =>
        let val tree = ref (mkTree (!depthRef, 0))
        in print "Running pass add1Tree (map): \n";
           sumTree (loop 0 (fn () => add1Tree (!tree)) (Leaf 0))
        end
    | "sum" =>
        let val tree = ref (mkTree (!depthRef, 0))
            val s = ref 0
        in print "Running pass sumTree (fold): \n";
           ignore (loop 0 (fn () => (s := sumTree (!tree); Leaf 0)) (Leaf 0));
           !s
        end
    | _ => raise Fail "pass must be build, add1 or sum"

fun fmt t =
  let val s = Real.fmt (StringCvt.FIX (SOME 9)) t
  in String.map (fn #"~" => #"-" | c => c) s end

val () = print ("ITER TIMES: [" ^ String.concatWith ", " (Array.foldr (op ::) [] (Array.tabulate (iters, fn i => fmt (Array.sub (times, i))))) ^ "]\n")
val () = print "End\n"
val () = print (Int64.toString answer ^ "\n")
