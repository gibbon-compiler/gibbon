datatype ('a, 'b) BinTree = Cell of 'a | Node of 'b  * ('a, 'b) BinTree * ('a, 'b) BinTree
datatype 'a Maybe = Just of 'a | Nothing | Error
datatype 'a PList = Nil | Cons of 'a * 'a PList
					  
fun length a =
    (case a of
	 Nil => 0
       | Cons (x, xs) => 1 + length xs)


fun head a =
    (case a of
	 Nil => raise Fail "error"
       | Cons (x, xs) => x)

fun tail a =
    (case a of
	 Nil => raise Fail "error"
       | Cons (_, xs) => xs)

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

fun filter f xs =
    (case xs of
	 Nil => Nil
       | Cons (x, xs) => if f x then Cons (x, filter f xs) else filter f xs)

fun fromto a b =
    if a > b then Nil else Cons (a, fromto (a + 1) b)

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

fun pid (PS (pid, _, _, _, _)) = pid
fun compType (PS (_, compType, _, _, _)) = compType
fun pathDepth (PS (_, _, pathDepth, _, _)) = pathDepth
fun inport (PS (_, _, _, inport, _)) = inport
fun outports (PS (_, _, _, _, outports)) = outports
fun setOutports (PS (pid, ct, pd, i, _)) outport = (PS (pid, ct, pd, i, outport))

fun nearest_power_of_two x =
    let fun h y =
	    if y >= x then
		y
	    else
		h (y * 2)
    in
	h 1
    end

val emptyState = PS (~1, None, ~1, Nil, Nil)

fun tabulate n f =
    if n < 0 then
	raise Fail "error"
    else if n = 0 then
	Nil
    else
	Cons (f n, tabulate (n - 1) f)

fun take n xs =
    if n < 0 then
	raise Fail "error"
    else if n = 0 then
	Nil
    else
	(case xs of
	     Nil => raise Fail "error"
	   | Cons (x, xs) => Cons (x, take (n - 1) xs))
				       
	     
fun pad_circuit (size, ins, outs, states) =
    let val p2 = nearest_power_of_two size
	val nrm = p2 - (length states)
	val es = tabulate nrm (fn _ => emptyState)
    in (p2, ins, outs, take p2 (append states es)) end

datatype Boolean = F | T
fun inv s =
    (case s of
	 T => F
       | F => T)
fun and2 x y = if x = T andalso y = T then T else F
fun or2 x y = if x = T orelse y = T then T else F
fun xor x y = if x = y then T else F
				       
type 'a Packet = Pid * int * 'a * bool * int * bool * int * int

val emptyPacket : Boolean Packet = (~1, ~1, F, false, 0, false, 0, 1)

fun send_right (ia, sa, ma, qla, dla, qra, dra, ea) (ib, sb, mb, qlb, dlb, qrb, drb, eb)
  = if qra andalso dra > eb
    then (ia, sa, ma, qla, dla, qra, dra - eb, ea + eb)
    else (ib, sb, mb, qlb, dlb, qrb, drb, ea + eb)

fun send_left (ia, sa, ma, qla, dla, qra, dra, ea) (ib, sb, mb, qlb, dlb, qrb, drb, eb)
  = if qlb andalso dlb > ea
    then (ib, sb, mb, qlb, dlb - ea, qrb, drb, ea + eb)
    else (ia, sa, ma, qla, dla, qra, dra, ea + eb)

fun send xs = scanlr send_right send_left emptyPacket emptyPacket xs

fun collect_outputs (size, ins, outs, states) =
    let val temp0 = filter (fn s => pid s = p) state
	val temp1 = map (fn s => head (inports s)) temp0
	fun third (_, _, v) = v
	fun get_output (label, p) = third (head temp1)
    in
	map get_output outs
    end

fun simulate inputs_list (size, ins, outs, states) = 
    let val circuit  = (size, ins, outs, states)
	val circuit' = (size, ins, outs, map init_dffs states)
	val cpd      = critical_path_depth circuit
    in
	tail (scanl (do_cycle cpd) circuit' inputs_list)
    end

fun circuit_simulate inputs_list circuit =
  map collect_outputs (simulate inputs_list circuit)
