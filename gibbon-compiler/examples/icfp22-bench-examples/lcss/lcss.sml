datatype 'a Plist = Nil | Cons of ('a * ('a Plist))

fun sndList tupleList =
    (case tupleList of
	 Nil => Nil
       | Cons (aVal, rst) =>
	 let val (a, b) = aVal
	 in Cons (b, (sndList rst)) end)

fun max (a, b) = if (a >= b) then a else b

fun ifalgb tell add max = if tell then add else max

fun algb2 x k0j1 k1j1 mList =
    (case mList of
	 Nil => Nil
       | Cons (aVal, ys) =>
	 let val (y, k0j) = aVal
	     val tell = (x = y)
	     val addVal = k0j1 + 1
	     val maxVal = max (k1j1, k0j)
	     val kjcurr = ifalgb tell addVal maxVal
	     val newTup = (y, kjcurr)
	 in Cons (newTup, algb2 x k0j kjcurr ys) end)

fun algb1 list1 ys' =
    (case list1 of
	 Nil => sndList ys'
       | Cons (x, xs) =>
	 algb1 xs (algb2 x 0 0 ys'))

fun zeroTupleList list =
    (case list of
	 Nil => Nil
       | Cons (y, rst) =>
	 Cons ((y, 0), zeroTupleList rst))

fun algb xs ys =
    Cons (0, algb1 xs (zeroTupleList ys))

fun zip list1 list2 =
    (case list1 of
	 Nil => Nil (* is this correct? --MR *)
       | Cons (a, rst) => (case list2 of
			       Nil => Nil
			     | Cons (b, rst') => Cons ((a, b), zip rst rst')))

fun mreverse xs acc =
    (case xs of
	 Nil => acc
       | Cons (z, zs) => mreverse zs (Cons (z, acc)))

fun elem a list =
    (case list of
	 Nil => false
       | Cons (x, rst) => if (x = a) then true else (false orelse (elem a rst)))

fun take num list =
    (case list of
	 Nil => Nil
       | Cons (x, rst) =>
	 if (num > 0) then Cons (x, take (num - 1) rst) else Nil)

fun drop num list =
    (case list of
	 Nil => Nil
       | Cons (x, rst) => if (num <= 0) then Cons (x, rst) else drop (num - 1) rst)


fun findk k km m list =
    (case list of
	 Nil => km
       | Cons (aVal, rst) =>
	 let val (x, y) = aVal
	 in if ( (x + y) >= m ) then findk (k + 1) k (x + y) rst
	    else findk (k + 1) km m rst
	 end)

fun ifalgc check list1 list2 = if check then list1 else list1

fun appendCons v tl = Cons (v, tl)

fun algc m n xs ys ys' =
    (case ys of
	 Nil => ys'
       | Cons (x, rst) =>
	 (case xs of
	      Nil => Nil
	    | Cons (x', rst') => (case rst' of
				      Nil => let val isElem = elem x' ys
						 val headList = appendCons x' ys'
						 val idList = ys'
					     in ifalgc isElem headList idList end
				    | Cons (x'', rst'') =>
				      let val m2 = m div 2
					  val xs1 = take m2 xs
					  val xs2 = drop m2 xs
					  val l1 = algb xs1 ys
					  val l2 = mreverse (algb (mreverse xs2 Nil) (mreverse ys Nil)) Nil
					  val k = findk 0 0 (~1) (zip l1 l2)
					  val algc' = algc (m - m2) (n - k) xs2 (drop k ys) ys'
					  val algc'' = algc m2 k xs1 (take k ys) algc'
				      in algc'' end)))

fun length' list =
    (case list of
	 Nil => 0
       | Cons (a, rst) => 1 + (length' rst))

fun lcss xs ys = algc (length' xs) (length' ys) xs ys Nil

fun makeIntList start e skipFactor =
    if (start <= e) then Cons (start, makeIntList (start + skipFactor) e skipFactor) else Nil

fun readArrayFile f =
    let val ins = TextIO.openIn f
	fun h () =
	    (case (TextIO.scanStream(Int.scan StringCvt.DEC) ins) of
		 NONE => []
	       | SOME (i:int) => i :: h ())
	val is = h ()
    in TextIO.closeIn ins;
       is
    end

fun bench_main () =
    let val iv = Vector.fromList (readArrayFile "lcss.faststdin")
	val a1 = Vector.sub (iv, 0)
	val b1 = Vector.sub (iv, 1)
	val c1 = Vector.sub (iv, 2)
	val d1 = Vector.sub (iv, 3)
	val e1 = Vector.sub (iv, 4)
	val f1 = Vector.sub (iv, 5)
	val l5 = makeIntList (Vector.sub (iv, 6)) (Vector.sub (iv, Vector.length iv - 1)) (Vector.sub (iv, 7) - Vector.sub (iv, 6))
	val l1 = makeIntList a1 c1 (b1 - a1)
	val l2 = makeIntList d1 f1 (e1 - d1)
	val l3 = lcss l1 l2
    in l3 end
