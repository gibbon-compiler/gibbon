type Key = int

datatype 'e Tree =
	 Node of Key * 'e Tree * 'e Tree
	 | Leaf of Key * 'e
	 | Empty
         | ErrorNode

type Entity = int * int * int * int
type Join = int * int * int * int * int

fun insertT k e t =
    (case t of
	 Node (k', l, r) => if k <= k' then Node (k', insertT k e l, r) else Node (k', l, insertT k e r)
       | Leaf (k', v) => if k < k' then Node (k, Leaf (k, e), Leaf (k', v))
			 else if k > k' then Node (k', Leaf (k', v), Leaf (k', e))
			 else ErrorNode
       | Empty => Leaf (k, e)
       | ErrorNode => ErrorNode)
	     
fun lookupT k n =
    (case n of
	 Node (k', l, r) => if k <= k' then lookupT k l else lookupT k r
      |  Leaf (k', e) => if k = k' then SOME e else NONE
      | Empty => NONE
      | ErrorNode => NONE)

fun mkTree fk pts t =
    let val n = Vector.length pts
	fun h fk i t =
	    if i >= n
	    then t
	    else let val pt = Vector.sub (pts, i)
		     val i' = i + 1
		     val k = fk pt
		 in h fk i' (insertT k pt t) end
    in h fk 0 t end

fun join t1 t2 j =
    (case t1 of
	 ErrorNode => ErrorNode
       | Empty => j
       | Leaf (k, v) =>
	 let val (a, b, c) = v
	     val t2' = lookupT c t2
	     val res = (case t2' of
			    NONE => j
			  | SOME w => let val (d, e, f) = w in insertT c (a, b, c, d, e) j end)
	 in (case t2 of
		 Empty => j
	       | Node _ => res
	       | Leaf _ => res
	       | ErrorNode => ErrorNode)
	 end
       | Node (k, l, r) =>
	 (case t2 of
	      Empty => j
	    | Node _ => join l t2 (join r t2 j)
	    | Leaf _ => join l t2 (join r t2 j)
	    | ErrorNode => ErrorNode))

fun readArrayFile f =
    let val ins = TextIO.openIn f
	fun h () =
	    (case (TextIO.inputLine ins) of
		 NONE => []
	       | SOME l => l :: h ())
	val ls = h ()
	val _ = TextIO.closeIn ins
	fun cvt l =
	    let val ts = String.tokens (fn c => c = #" ") l
		val [i1, i2, i3] = List.map (Option.valOf o Int.fromString) ts
	    in
		(i1, i2, i3)
	    end
    in 
       List.map cvt ls
    end

fun bench_main () =
    let val f = Vector.fromList (readArrayFile "treejoin.txt")
	val len = Vector.length f
	val half = len div 2
	val f1 = Vector.tabulate (half, fn i => Vector.sub (f, i))
	val f2 = Vector.tabulate (len - half, fn i => Vector.sub (f, half + i))
	val fk = fn (x, _, _) => x
	val t1 = mkTree fk f1 Empty
	val t2 = mkTree fk f1 Empty
	val _ = join t1 t2 Empty
    in () end
