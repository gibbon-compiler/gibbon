datatype 'a PList = Nil | Cons of 'a * 'a PList

fun length a =
    (case a of
	 Nil => 0
       | Cons (x, xs) => 1 + length xs)


fun head a =
    (case a of
	 Nil => raise Fail "error"
       | Cons (x, xs) => x)

fun append a b =
    (case a of
	 Nil => b
       | Cons (x, xs) => Cons (x, append xs b))

fun splitAt n a =
    if n = 0 then
	(Nil, a)
    else
	(case a of
	     Nil => raise Fail "error"
	   | Cons (x, xs) =>
	     let val (c, d) = splitAt (n - 1) xs
	     in (Cons (x, c), d) end)
	    
fun map f a =
    (case a of
	 Nil => Nil
       | Cons (x, xs) => Cons (f x, map f xs))

fun concat as1 =
    (case as1 of
	 Nil => Nil
       | Cons (x, xs) =>
	 let val y = concat xs in append x y end)

fun zipWith as1 bs =
    (case as1 of
	 Nil => Nil
       | Cons (x, xs) =>
	 (case bs of
	      Nil => Nil
	    | Cons (y, ys) => Cons ((x, y), zipWith xs ys)))

fun fromto a b =
    if a > b then Nil else Cons (a, fromto (a + 1) b)

datatype ('a, 'b) BinTree = Cell of 'a | Node of 'b  * ('a, 'b) BinTree * ('a, 'b) BinTree
datatype 'a Maybe = Just of 'a | Nothing | Error

fun put xs =
    if length xs = 1 then
	Cell (head xs)
    else
	let val (fstHalf, sndHalf) = splitAt ((length xs) div 2) xs
	in
	    Node ((), put fstHalf,  put sndHalf)
	end
	    
fun get tree =
    (case tree of
	 Cell x => Cons (x, Nil)
       | Node (x, l, r)  => append (get l) (get r))

fun upsweep f tree =
    (case tree of
	 Cell a => (a, Cell a)
       | Node (x, l, r) =>
	 let val (lv, l') = upsweep f l
	     val (rv, r') = upsweep f r
	 in
	     (f lv rv, Node ((lv, rv), l', r'))
	end)

fun downsweep g d tree =
    (case tree of
	 Cell x => Cell d
       | Node (lrv, l, r) =>
	 let val (lv, rv) = lrv
	     val (dl, dr) = g lv rv d
	     val (l', r') = (downsweep g dl l, downsweep g dr r)
	 in
	     Node ((), l', r')
	 end)
	
fun sweep_ud (up : 'a -> 'a -> 'a)
	     (down : 'a -> 'a -> 'b -> ('b * 'b))
	     (u : 'b)
	     (t : ('a, 'c) BinTree)
    : 'a * ('b, unit) BinTree =
    let val (ans, t') = upsweep up t
    in (ans, downsweep down u t') end

fun scanL f u xs =
    let	fun down l r x = (x, f x l)
	val (up_ans, t') = sweep_ud f down u (put xs)
    in
	(up_ans, get t')
    end

fun scanR f u xs =
    let fun down l r x = (f r x, x)
	val (up_ans, t') = sweep_ud f down u (put xs)
    in
	(up_ans, get t')
    end

fun scanlr (f : 'a -> 'a -> 'a) (g : 'a -> 'a -> 'a) (lu : 'a) (ru : 'a) (xs : 'a PList) =
    let fun down (lx, ly) (rx, ry) (a, b) = ((a, g ry b), (f a lx, b))
	fun up (lx, ly) (rx, ry) = (f lx rx, g ly ry)
	val xs' = map (fn x => (x, x)) xs
	val ((l_ans, r_ans), t) = sweep_ud up down (lu, ru) (put xs')
	val ans = (g r_ans ru, f lu l_ans)
    in
	(ans, get t)
    end

type Pid = int
type Label = string * Pid
datatype Component =
	 None
       | Inp
       | Outp
       | Dff
       | Inv
       | And2
       | Or2
       | Xor
type 'a InPort = Pid * int * 'a
type 'a OutPort = int * 'a * bool * int * bool * int
datatype 'a State = PS of int * Component * int * ('a InPort) PList * ('a OutPort) PList
type 'a Circuit = int * Label PList * Label PList * ('a State) PList
									    
