-- https://github.com/ghc/nofib/blob/f34b90b5a6ce46284693119a06d1133908b11856/gc/circsim/Main.lhs
-- data BinTree a b = Cell a | Node b (BinTree a b) (BinTree a b)
-- data Maybe a = Just a | Nothing | Error
data PList a = Nil | Cons a (PList a)


length :: PList a -> Int
length a = case a of
  Nil       -> 0
  Cons x xs -> 1 + length xs

head :: PList a -> a
head a = case a of
  Nil       -> error
  Cons x xs -> x

(++) :: PList a -> PList a -> PList a
(++) a b = case a of
  Nil       -> b
  Cons x xs -> Cons x ((++) xs b)

splitAt :: Int -> PList a -> (PList a, PList a)
splitAt n a = if n == 0
  then (Nil, a)
  else case a of
    Nil       -> error
    Cons x xs -> let (c, d) = splitAt (n - 1) xs in (Cons x c, d)

map :: (a -> b) -> PList a -> PList b
map f a = case a of
  Nil       -> Nil
  Cons x xs -> Cons (f x) (map f xs)

concat :: PList (PList a) -> PList a
concat as = case as of
  Nil       -> Nil
  Cons x xs -> let y = concat xs in x ++ y

zipWith :: PList a -> PList b -> (a, b)
zipWith as bs = case as of
  Nil       -> Nil
  Cons x xs -> case bs of
    Nil       -> Nil
    Cons y ys -> Cons (x, y) (zipWith xs ys)

fromto :: Int -> Int -> PList Int 
fromto a b = if  a > b then  Nil else  Cons a (fromto (a+1) b)

put :: PList a -> BinTree a ()
put xs = if length xs == 1
  then Cell (head xs)
  else
    let (fstHalf, sndHalf) = splitAt (div (length xs) 2) xs
    in  Node () (put fstHalf) (put sndHalf)

get :: BinTree a b -> PList a
get tree = case tree of
  Cell x     -> Cons x Nil
  Node x l r -> get l ++ get r

upsweep :: (a -> a -> a) -> BinTree a b -> (a, BinTree a (a, a))
upsweep f tree = case tree of
  Cell a     -> (a, Cell a)
  Node x l r -> (f lv rv, Node (lv, rv) l' r')
 where
  (lv, l') = upsweep f l
  (rv, r') = upsweep f r

downsweep :: (a -> b -> c -> (c, c)) -> c -> BinTree d (a, b) -> BinTree c ()
downsweep g d tree = case tree of
  Cell x       -> Cell d
  Node lrv l r -> Node () l' r'
 where
  (lv, rv) = lrv
  (dl, dr) = g lv rv d
  (l', r') = (downsweep g dl l, downsweep g dr r)

sweep_ud
  :: (a -> a -> a)
  -> (a -> a -> b -> (b, b))
  -> b
  -> BinTree a c
  -> (a, BinTree b ())

sweep_ud up down u t = (ans, downsweep down u t')
  where (ans, t') = upsweep up t

scanL :: (a -> a -> a) -> a -> PList a -> (a, PList a)
scanL f u xs = (up_ans, get t')
 where
  (up_ans, t') = sweep_ud f down u (put xs)
  down l r x = (x, f x l)

scanR :: (a -> a -> a) -> a -> PList a -> (a, PList a)
scanR f u xs = (up_ans, get t')
 where
  (up_ans, t') = sweep_ud f down u (put xs)
  down l r x = (f r x, x)

scanlr
  :: (a -> a -> a) -> (a -> a -> a) -> a -> a -> PList a -> ((a, a), PList (a, a))
scanlr f g lu ru xs = (ans, get t)
 where
  ((l_ans, r_ans), t) = sweep_ud up down (lu, ru) (put xs')
  ans                 = (g r_ans ru, f lu l_ans)
  xs'                 = map (\x -> (x, x)) xs
  up (lx, ly) (rx, ry) = (f lx rx, g ly ry)
  down (lx, ly) (rx, ry) (a, b) = ((a, g ry b), (f a lx, b))

type Circuit a = (Int, PList Label, PList Label, PList (State a))

type Label = (String, Pid)

type Pid = Int

data Component
      = None  -- no component
      | Inp   -- input to the entire circuit
      | Outp  -- output from the entire circuit
      | Dff   -- delay flip flop
      | Inv   -- inverter
      | And2  -- 2-input and gate
      | Or2   -- 2-input or gate
      | Xor   -- exclusive or gate
      deriving (Eq, Show)

data State a = PS Int Component Int (PList (InPort a)) (PList (OutPort a))
pid st = case st of
  PS pid _ _ _ _ -> pid
compType st = case st of
  PS _ compType _ _ _ -> compType
pathDepth st = case st of
  PS _ _ pathDepth _ _ -> pathDepth
inport st = case st of
  PS _ _ _ inports _ -> inports
outports st = case st of
  PS _ _ _ _ outports -> outports
setOutports st o = case st of
  PS pid ct pd i _ -> PS pid ct pd i o

type InPort a = (Pid, Int, a)

type OutPort a = (Int, a, Bool, Int, Bool, Int)


nearest_power_of_two :: Int -> Int
nearest_power_of_two x = until (\y -> y >= x) (\y -> y * 2) 1

pad_circuit :: Circuit a -> Circuit a
pad_circuit (size, ins, outs, states) =
  (p2, ins, outs, take p2 (states ++ repeat emptyState))
  where p2 = nearest_power_of_two size

emptyState :: State a
emptyState = PS (-1) None (-1) Nil Nil

data Boolean = F | T
inv s = case s of
  T -> F
  F -> T
and2 x y = if x == T && y == T then T else F
or2 x y = if x == T || y == T then T else F
xor x y = if x == y then T else F

type Packet a = (Pid, Int, a, Bool, Int, Bool, Int, Int)

emptyPacket :: Packet a
emptyPacket = (-1, -1, F, False, 0, False, 0, 1)

send_right :: Packet a -> Packet a -> Packet a
send_right (ia, sa, ma, qla, dla, qra, dra, ea) (ib, sb, mb, qlb, dlb, qrb, drb, eb)
  = if qra && dra > eb
    then (ia, sa, ma, qla, dla, qra, dra - eb, ea + eb)
    else (ib, sb, mb, qlb, dlb, qrb, drb, ea + eb)

send_left :: Packet a -> Packet a -> Packet a
send_left (ia, sa, ma, qla, dla, qra, dra, ea) (ib, sb, mb, qlb, dlb, qrb, drb, eb)
  = if qlb && dlb > ea
    then (ib, sb, mb, qlb, dlb - ea, qrb, drb, ea + eb)
    else (ia, sa, ma, qla, dla, qra, dra, ea + eb)

send :: PList (Packet a) -> ((Packet a, Packet a), PList (Packet a, Packet a))
send xs = scanlr send_right send_left emptyPacket emptyPacket xs

circuit_simulate :: PList (PList a) -> Circuit a -> PList (PList a)
circuit_simulate inputs_list circuit =
  map collect_outputs (simulate inputs_list circuit)

collect_outputs :: Circuit a -> PList a
collect_outputs (size, ins, outs, states) = map get_output outs
 where
  temp0 = filter (\s -> pid s == p) state
  temp1 = map (\s -> head (inports s)) temp0
  get_output (label, p) = third (head temp1)
  third (_, _, v) = v

simulate :: PList (PList a) -> Circuit a -> PList (Circuit a)
simulate inputs_list (size, ins, outs, states) = tail
  (scanl (do_cycle cpd) circuit' inputs_list)
 where
  circuit  = (size, ins, outs, states)
  circuit' = (size, ins, outs, map init_dffs states)
  cpd      = critical_path_depth circuit

do_cycle :: Int -> Circuit a -> PList a -> Circuit a
do_cycle cpd (size, ins, outs, states) inputs = (size, ins, outs, states4)
 where
  states1 = map (store_inputs (zip ins inputs)) states
  states2 = do_sends 0 states1
  states3 = foldl sim_then_send states2 [1 .. cpd]
  sim_then_send state d = do_sends d (simulate_components d state)
  states4 = restore_requests states states3

restore_requests :: PList (State a) -> PList (State a) -> PList (State a)
restore_requests old_states new_states = zipWith restore old_states new_states
 where
  restore os ns =
    ns { outports = zipWith restore_outport (outports os) (outports ns) }
  restore_outport (p, _, ql, dl, qr, dq) (_, m, _, _, _, _) =
    (p, m, ql, dl, qr, dq)

do_sends :: Int -> PList (State a) -> PList (State a)
do_sends d states = until (acknowledge d) (do_send d) states

acknowledge :: Int -> PList (State a) -> Bool
acknowledge d states = not (or (map (check_requests . outports) states1))
 where
  check_requests xs = or (map check_lr_requests xs)
  check_lr_requests (p, m, ql, dl, qr, dr) = ql || qr
  states1 = map (check_depth d) states

do_send :: Int -> PList (State a) -> PList (State a)
do_send d states = zipWith (update_io d) pss' states
 where
  states1      = map (check_depth d) states
  pss          = (transpose . pad_packets) (map make_packet states1)
  send_results = map (snd . send) pss
  pss'         = transpose send_results

update_io :: Int -> PList (Packet a, Packet a) -> State a -> State a
update_io d lrps state = update_os (update_is state)
 where
  update_is state = state { inports = foldr update_i (inports state) lrps }
  update_os state = if pathDepth state == d
    then state { outports = zipWith update_o lrps (outports state) }
    else state

update_o :: (Packet a, Packet a) -> OutPort a -> OutPort a
update_o (lp, rp) out = check_left lp (check_right rp out)

check_left (pid, port, pm, pql, pdl, pqr, pdr, e) (p, m, ql, dl, qr, dr) =
  if pqr && pdr > 0 then (p, m, ql, dl, qr, dr) else (p, m, ql, dl, False, dr)
check_right (pid, port, pm, pql, pdl, pqr, pdr, e) (p, m, ql, dl, qr, dr) =
  if pql && pdl > 0 then (p, m, ql, dl, qr, dr) else (p, m, False, dl, qr, dr)

update_i :: (Packet a, Packet a) -> PList (InPort a) -> PList (InPort a)
update_i (l, r) ins = up_i l (up_i r ins)

up_i :: Packet a -> PList (InPort a) -> PList (InPort a)
up_i (i, p, m', _, _, _, _, _) ins = map (compare_and_update (i, p, m')) ins

compare_and_update :: InPort a -> InPort a -> InPort a
compare_and_update (i, p, m') (pid, port, m) =
  if (i, p) == (pid, port) then (pid, port, m') else (pid, port, m)

make_packet :: State a -> PList (Packet a)
make_packet state = map
  (\(p, m, ql, dl, qr, dr) -> (pid state, p, m, ql, dl, qr, dr, 1))
  (outports state)

pad_packets :: PList (PList (Packet a)) -> PList (PList (Packet a))
pad_packets pss = map pad pss
 where
  pad xs = take max_ps (xs ++ repeat emptyPacket)
  max_ps = maximum (map length pss)

check_depth :: Int -> State a -> State a
check_depth d state =
  if pathDepth state == d then state else update_requests False state

update_requests :: Bool -> State a -> State a
update_requests b state =
  let outports' =
        map (\(p, m, ql, dl, qr, dr) -> (p, m, b, dl, b, dr)) (outports state)
  in  setOutports state outports'

simulate_components :: Int -> PList (State a) -> PList (State a)
simulate_components depth states = map (simulate_component depth) states

simulate_component :: Int -> State a -> State a
simulate_component d state = case new_value of
  Nothing -> state
  Just v  -> if d == pathDepth state then update_outports state v else state
 where
  out_signals = [ sig | (_, _, sig) <- inports state ]
  new_value   = apply_component (compType state) out_signals

apply_component :: Component -> PList a -> Maybe a
apply_component comp inp = case comp of
  Inp  -> Nothing
  Outp -> Just x
  Dff  -> Just x
  Inv  -> Just (inv x)
  And2 -> Just (and2 x y)
  Or2  -> Just (or2 x y)
  Xor  -> Just (xor x y)
 where
  x = vnth inp 1
  y = vnth inp 2

store_inputs :: PList (Label, a) -> State a -> State a
store_inputs label_inputs state = if compType state == Inp
  then head
    (map
      (\((label, input_pid), value) -> update_outports state value)
      (filter (\((label, input_pid), value) -> pid state == input_pid)
              label_inputs
      )
    )
  else state


init_dffs :: State a -> State a
init_dffs state =
  if compType state == Dff then update_outports state F else state


critical_path_depth :: Circuit a -> Int
critical_path_depth (size, ins, outs, states) = maximum (map pathDepth states)


input_values :: Int -> PList (PList a)
input_values nbits = map binary (generate (2 ^ nbits - 1) (\x -> x))
 where
  binary n = map int2sig (reverse (take nbits (bin n ++ repeat 0)))
  int2sig s = if (s == 0) then F else one
  bin 0 = []
  bin n = r : bin q where (q, r) = n `quotRem` 2


update_outports :: State a -> a -> State a
update_outports state value = setOutports
  state
  (map (\(p, m, ql, dl, qr, dr) -> (p, value, ql, dl, qr, dr)) outs)
  where outs = outports state


regs :: Int -> Circuit a
regs bits = let 
    size = 1 + 7 * bits
    states =
      Cons sto (concat (map (reg 0) (map (\x -> 7*x+1) (fromto 0 (bits-1)))))
    sto = PS 0 Inp 0 Nil (Cons (0, F, False, 0, True, 8 * (bits - 1) + 5) Nil)
  in   (size, states)

reg :: Pid -> Pid -> PList (State Boolean)
reg sto n =
  let reg0, reg1, reg2, reg3, reg4, reg5, reg6, reg7 :: PList (State Boolean)
      in1, in2, in3, in4, in5, in6, in7 :: PList (Pid, Int, Boolean)
      out1, out2, out3, out4, out5, out6, out7 :: PList (Int, Boolean, Bool, Int, Bool, Int)
      reg0 = Nil
      in1  = Nil
      out1 = Cons (0, F, False, 0, True, 4) Nil
      reg1 = Cons (PS n Inp 0 in1 out1) reg0
      in2  = Cons (n + 5, 0, F) Nil
      out2 = Cons (0, F, False, 0, True, 5) Nil
      reg2 = Cons (PS (n + 1) Dff 1 in2 out2) reg1
      in3  = Cons (sto, 0, F) Nil
      out3 = Cons (0, F, False, 0, True, 1) Nil
      reg3 = Cons (PS (n + 2) Inv 1 in3 out3) reg2
      in4  = Cons (n + 1, 0, F) (Cons (n + 2, 0, F) Nil)
      out4 = Cons (0, F, False, 0, True, 2) Nil
      reg4 = Cons (PS (n + 3) And2 2 in4 out4) reg3
      in5  = Cons (sto, 0, F) (Cons (n, 0, F) Nil)
      out5 = Cons (0, F, False, 0, True, 1) Nil
      reg5 = Cons (PS (n + 4) And2 1 in5 out5) reg4
      in6  = Cons (n + 3, 0, F) (Cons (n + 4, 0, F) Nil)
      out6 = Cons (0, F, True, 4, False, 0) Nil
      reg6 = Cons (PS (n + 5) Or2 3 in6 out6) reg5
      in7  = Cons (n + 1, 0, F) Nil
      out7 = Nil
      reg7 = Cons (PS (n + 6) Outp 4 in7 out7) reg6
  in  reg7

run num_bits num_cycles =
  let example = pad_circuit (regs num_bits)
      inputs  = generate (num_bits + 1) (\_ -> T)
      cycles  = generate num_cycles (\_ -> inputs)
  in  circuit_simulate cycles example


bench_main :: ()
bench_main = let _ = run 8 1000 in ()

gibbon_main = bench_main
