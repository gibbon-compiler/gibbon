-- https://github.com/ghc/nofib/blob/f34b90b5a6ce46284693119a06d1133908b11856/gc/circsim/Main.lhs
-- module Main where
-- import Prelude hiding (map, concat,head,length,splitAt,zipWith,Just,Nothing,Maybe,repeat,reverse,take,filter,foldr,foldl,zip,scanl,tail,maximum,or)
-- main = print 0

data BinTree a b = Cell a | Node b (BinTree a b) (BinTree a b)
data Maybe a = Just a | Nothing | Error
data PList a = Nil | Cons a (PList a)

-- generate = undefined
-- vnth = undefined

transpose :: PList (PList a) -> PList (PList a)
transpose a = Cons (map head a) (transpose (map tail a))

zip :: PList a -> PList b -> PList (a, b)
zip as bs =
  case as of 
    Nil -> Nil 
    Cons z zs -> case bs of 
      Nil -> Nil 
      Cons y ys -> Cons (z, y) (zip zs ys)

not :: Bool -> Bool
not a = if a then False else True

maximum :: PList Int -> Int 
maximum a = 
  case a of 
    Nil -> 0 
    Cons z zs -> let m = maximum zs in if z > m then z else m

foldr :: (a -> b -> b) -> b -> PList a -> b 
-- foldr f z [x1, x2, ..., xn] == x1 `f` (x2 `f` ... (xn `f` z)...)
foldr f z a = 
  case a of 
    Nil -> z 
    Cons z1 zs -> f z1 (foldr f z zs)

or :: PList Bool -> Bool 
or a = case a of 
  Nil -> True 
  Cons z zs -> z || (or zs)

scanl :: (b -> a -> b) -> b -> PList a -> PList b
-- scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
scanl f z as = 
  case as of 
    Nil -> Cons z Nil
    Cons a as' -> Cons z (scanl f (f z a) as')

tail :: PList a -> PList a 
tail a = case a of
  Nil -> Nil 
  Cons z zs -> zs

foldl :: (b -> a -> b) -> b -> PList a -> b
--  foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
foldl f z a = 
  case a of 
    Nil -> z 
    Cons z1 zs -> foldl f (f z z1) zs

filter :: (a -> Bool) -> PList a -> PList a 
filter f a = 
  case a of 
    Nil -> Nil 
    Cons z zs -> if f z then Cons z (filter f zs) else filter f zs

take :: Int -> PList a -> PList a
take n a = 
  if n == 0 
    then Nil 
  else 
    case a of 
      Nil -> Nil 
      Cons z zs -> Cons z (take (n-1) zs)

length :: PList a -> Int
length a = case a of
  Nil       -> 0
  Cons x xs -> 1 + length xs

head :: PList a -> a
head a = case a of
  Nil       -> head a -- error 
  Cons x xs -> x

repeat :: a -> PList a 
repeat x = Cons x (repeat x)

reverse_go :: PList a -> PList a -> PList a
reverse_go b acc = 
    case b of 
      Nil -> acc 
      Cons z zs -> reverse_go zs (Cons z acc)

reverse :: PList a -> PList a 
reverse a = reverse_go a Nil 

app :: PList a -> PList a -> PList a
app a b = case a of
  Nil       -> b
  Cons x xs -> Cons x (app xs b)

splitAt :: Int -> PList a -> (PList a, PList a)
splitAt n a = if n == 0
  then (Nil, a)
  else case a of
    Nil       -> (Nil, Nil) -- error case
    Cons x xs -> let (c, d) = splitAt (n - 1) xs in (Cons x c, d)

map :: (a -> b) -> PList a -> PList b
map f a = case a of
  Nil       -> Nil
  Cons x xs -> Cons (f x) (map f xs)

until :: (a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x then x else until p f (f x)

concat :: PList (PList a) -> PList a
concat as = case as of
  Nil       -> Nil
  Cons x xs -> let y = concat xs in app x y

zipWith :: (a -> b -> c) -> PList a -> PList b -> PList c
zipWith f as bs = case as of
  Nil       -> Nil
  Cons x xs -> case bs of
    Nil       -> Nil
    Cons y ys -> Cons (f x y) (zipWith f xs ys)

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
  Node x l r -> app (get l) (get r)

upsweep :: (a -> a -> a) -> BinTree a b -> (a, BinTree a (a, a))
upsweep f tree = case tree of
  Cell a     -> (a, Cell a)
  Node x l r -> 
    let 
      (lv, l') = upsweep f l
      (rv, r') = upsweep f r
    in 
      (f lv rv, Node (lv, rv) l' r')        

downsweep :: (a -> b -> c -> (c, c)) -> c -> BinTree d (a, b) -> BinTree c ()
downsweep g d tree = case tree of
  Cell x       -> Cell d
  Node lrv l r -> 
    let 
      (lv, rv) = lrv
      (dl, dr) = g lv rv d
      (l', r') = (downsweep g dl l, downsweep g dr r)
    in Node () l' r'

sweep_ud
  :: (a -> a -> a)
  -> (a -> a -> b -> (b, b))
  -> b
  -> BinTree a c
  -> (a, BinTree b ())

sweep_ud up down u t = 
  let (ans, t') = upsweep up t
  in (ans, downsweep down u t')

scanL :: (a -> a -> a) -> a -> PList a -> (a, PList a)
scanL f u xs = 
  let 
    down l r x = (x, f x l)
    (up_ans, t') = sweep_ud f down u (put xs)
  in (up_ans, get t')

scanR :: (a -> a -> a) -> a -> PList a -> (a, PList a)
scanR f u xs = 
  let 
    down l r x = (f r x, x)
    (up_ans, t') = sweep_ud f down u (put xs)
  in (up_ans, get t')

scanlr
  :: (a -> a -> a) -> (a -> a -> a) -> a -> a -> PList a -> ((a, a), PList (a, a))
scanlr f g lu ru xs = 
  let
    up (lx, ly) (rx, ry) = (f lx rx, g ly ry)
    down (lx, ly) (rx, ry) (a, b) = ((a, g ry b), (f a lx, b))
    xs'                 = map (\x -> (x, x)) xs
    (v1, t) = sweep_ud up down (lu, ru) (put xs')
    (l_ans, r_ans)      = v1 
    ans                 = (g r_ans ru, f lu l_ans)
  in (ans, get t)

-- type Circuit a = (Int, PList Label, PList Label, PList (State))
type Label = (Int, Int)

-- type Int = Int

data Component
      = None  -- no component
      | Inp   -- input to the entire circuit
      | Outp  -- output from the entire circuit
      | Dff   -- delay flip flop
      | Inv   -- inverter
      | And2  -- 2-input and gate
      | Or2   -- 2-input or gate
      | Xor   -- exclusive or gate
compare_None :: Component -> Bool
compare_None b = case b of
        None -> True
        Inp -> False
        Outp -> False
        Dff -> False
        Inv -> False
        And2 -> False
        Or2 -> False
        Xor -> False
compare_Inp :: Component -> Bool
compare_Inp b = case b of
        None -> False
        Inp -> True
        Outp -> False
        Dff -> False
        Inv -> False
        And2 -> False
        Or2 -> False
        Xor -> False
compare_Outp :: Component -> Bool
compare_Outp b = case b of
        None -> False
        Inp -> False
        Outp -> True
        Dff -> False
        Inv -> False
        And2 -> False
        Or2 -> False
        Xor -> False
compare_Dff :: Component -> Bool
compare_Dff b = case b of
        None -> False
        Inp -> False
        Outp -> False
        Dff -> True
        Inv -> False
        And2 -> False
        Or2 -> False
        Xor -> False
compare_Inv :: Component -> Bool
compare_Inv b = case b of
        None -> False
        Inp -> False
        Outp -> False
        Dff -> False
        Inv -> True
        And2 -> False
        Or2 -> False
        Xor -> False
compare_And2 :: Component -> Bool
compare_And2 b = case b of
        None -> False
        Inp -> False
        Outp -> False
        Dff -> False
        Inv -> False
        And2 -> True
        Or2 -> False
        Xor -> False
compare_Or2 :: Component -> Bool
compare_Or2 b = case b of
        None -> False
        Inp -> False
        Outp -> False
        Dff -> False
        Inv -> False
        And2 -> False
        Or2 -> True
        Xor -> False
compare_Xor :: Component -> Bool
compare_Xor b = case b of
        None -> False
        Inp -> False
        Outp -> False
        Dff -> False
        Inv -> False
        And2 -> False
        Or2 -> False
        Xor -> True
eqC :: Component -> Component -> Bool
eqC a b = case a of 
    None -> compare_None b
    Inp -> compare_Inp b
    Outp -> compare_Outp b
    Dff -> compare_Dff b
    Inv -> compare_Inv b
    And2 -> compare_And2 b
    Or2 -> compare_Or2 b
    Xor -> compare_Xor b

-- data State = PS Int Component Int (PList (InPort a)) (PList (OutPort a))
data State = PS Int Component Int (PList (Int, Int, Boolean)) (PList (Int, Boolean, Bool, Int, Bool, Int))
pid :: State -> Int
pid st = case st of
  PS pid _ _ _ _ -> pid
compType :: State -> Component
compType st = case st of
  PS _ compType _ _ _ -> compType
pathDepth :: State -> Int
pathDepth st = case st of
  PS _ _ pathDepth _ _ -> pathDepth
inports :: State -> PList (Int, Int, Boolean)
inports st = case st of
  PS _ _ _ inports _ -> inports
outports :: State -> PList (Int, Boolean, Bool, Int, Bool, Int)
outports st = case st of
  PS _ _ _ _ outports -> outports
setInports :: State -> PList (Int, Int, Boolean) -> State
setInports st i = case st of
  PS pid ct pd _ o -> PS pid ct pd i o
setOutports :: State -> PList (Int, Boolean, Bool, Int, Bool, Int) -> State
setOutports st o = case st of
  PS pid ct pd i _ -> PS pid ct pd i o

-- type InPort a = (Int, Int, Boolean)

-- type OutPort a = (Int, a, Bool, Int, Bool, Int)


nearest_power_of_two :: Int -> Int
nearest_power_of_two x = until (\y -> y >= x) (\y -> y * 2) 1

-- pad_circuit :: Circuit a -> Circuit a
pad_circuit :: (Int, PList Label, PList Label, PList (State)) -> (Int, PList Label, PList Label, PList (State))
pad_circuit (size, ins, outs, states) =
  let p2 = nearest_power_of_two size 
  in (p2, ins, outs, take p2 (app states (repeat emptyState)))

-- emptyState :: State
emptyState :: State
emptyState = PS (-1) None (-1) Nil Nil

data Boolean = F | T 
eq :: Boolean -> Boolean -> Bool
eq x y = 
  case x of 
    F -> 
      case y of 
        F -> True
        T -> False
    T -> 
      case y of 
        F -> False 
        T -> True
inv :: Boolean -> Boolean
inv s = case s of
  T -> F
  F -> T
and2 :: Boolean -> Boolean -> Boolean
and2 x y = if (eq x T) && (eq y T) then T else F
or2 :: Boolean -> Boolean -> Boolean
or2 x y = if (eq x T) || (eq y T) then T else F
xor :: Boolean -> Boolean -> Boolean
xor x y = if eq x y then T else F

-- type Packet a = (Int, Int, Boolean, Bool, Int, Bool, Int, Int)

-- emptyPacket :: Packet a
emptyPacket :: (Int, Int, Boolean, Bool, Int, Bool, Int, Int)
emptyPacket = (-1, -1, F, False, 0, False, 0, 1)

-- send_right :: Packet a -> Packet a -> Packet a
send_right :: (Int, Int, Boolean, Bool, Int, Bool, Int, Int) -> (Int, Int, Boolean, Bool, Int, Bool, Int, Int) -> (Int, Int, Boolean, Bool, Int, Bool, Int, Int)
send_right (ia, sa, ma, qla, dla, qra, dra, ea) (ib, sb, mb, qlb, dlb, qrb, drb, eb)
  = if qra && dra > eb
    then (ia, sa, ma, qla, dla, qra, dra - eb, ea + eb)
    else (ib, sb, mb, qlb, dlb, qrb, drb, ea + eb)

-- send_left :: Packet a -> Packet a -> Packet a
send_left :: (Int, Int, Boolean, Bool, Int, Bool, Int, Int) -> (Int, Int, Boolean, Bool, Int, Bool, Int, Int) -> (Int, Int, Boolean, Bool, Int, Bool, Int, Int)
send_left (ia, sa, ma, qla, dla, qra, dra, ea) (ib, sb, mb, qlb, dlb, qrb, drb, eb)
  = if qlb && dlb > ea
    then (ib, sb, mb, qlb, dlb - ea, qrb, drb, ea + eb)
    else (ia, sa, ma, qla, dla, qra, dra, ea + eb)

-- send :: PList (Packet a) -> ((Packet a, Packet a), PList (Packet a, Packet a))
send :: PList (Int, Int, Boolean, Bool, Int, Bool, Int, Int) -> (((Int, Int, Boolean, Bool, Int, Bool, Int, Int), (Int, Int, Boolean, Bool, Int, Bool, Int, Int)), PList ((Int, Int, Boolean, Bool, Int, Bool, Int, Int), (Int, Int, Boolean, Bool, Int, Bool, Int, Int)))
send xs = scanlr send_right send_left emptyPacket emptyPacket xs

-- circuit_simulate :: PList (PList a) -> Circuit a -> PList (PList a)
circuit_simulate :: PList (PList Boolean) -> (Int, PList Label, PList Label, PList (State)) -> PList (PList Boolean)
circuit_simulate inputs_list circuit =
  map collect_outputs (simulate inputs_list circuit)

-- collect_outputs :: Circuit a -> PList a
collect_outputs :: (Int, PList Label, PList Label, PList (State)) -> PList Boolean
collect_outputs (size, ins, outs, states) = 
  let 
    l1 p s = pid s == p
    temp0 p = filter (l1 p) states
    l2 s = head (inports s)
    temp1 p = map l2 (temp0 p)
    third (_, _, v) = v
    get_output (label, p) = third (head (temp1 p))
  in map get_output outs

-- simulate :: PList (PList a) -> Circuit a -> PList (Circuit a)
simulate :: PList (PList Boolean) -> (Int, PList Label, PList Label, PList (State)) -> PList ((Int, PList Label, PList Label, PList (State)))
simulate inputs_list (size, ins, outs, states) = 
  let 
    circuit  = (size, ins, outs, states)
    circuit' = (size, ins, outs, map init_dffs states)
    cpd      = critical_path_depth circuit
  in tail (scanl (do_cycle cpd) circuit' inputs_list)
  

-- do_cycle :: Int -> Circuit a -> PList a -> Circuit a
do_cycle :: Int -> (Int, PList Label, PList Label, PList (State)) -> PList Boolean -> (Int, PList Label, PList Label, PList (State))
do_cycle cpd (size, ins, outs, states) inputs = 
  let 
    states1 = map (store_inputs (zip ins inputs)) states
    states2 = do_sends 0 states1
    sim_then_send state d = do_sends d (simulate_components d state)
    states3 = foldl sim_then_send states2 (fromto 1 cpd)
    states4 = restore_requests states states3
  in (size, ins, outs, states4)

-- restore_requests :: PList (State) -> PList (State) -> PList (State)
restore_requests :: PList (State) -> PList (State) -> PList (State)
restore_requests old_states new_states = 
  let 
    restore_outport (p, _, ql, dl, qr, dq) (_, m, _, _, _, _) =
      (p, m, ql, dl, qr, dq)
    restore os ns =
      setOutports ns (zipWith restore_outport (outports os) (outports ns))
  in zipWith restore old_states new_states
 

-- do_sends :: Int -> PList (State) -> PList (State)
do_sends :: Int -> PList (State) -> PList (State)
do_sends d states = until (acknowledge d) (do_send d) states

-- acknowledge :: Int -> PList (State) -> Bool
acknowledge :: Int -> PList (State) -> Bool
acknowledge d states = 
  let 
    check_lr_requests (p, m, ql, dl, qr, dr) = ql || qr
    check_requests xs = or (map check_lr_requests xs)
    states1 = map (check_depth d) states
  in not (or (map (\x -> check_requests (outports x)) states1))

-- do_send :: Int -> PList (State) -> PList (State)
do_send :: Int -> PList (State) -> PList (State)
do_send d states = 
  let
    states1      = map (check_depth d) states
    pss          = transpose (pad_packets (map make_packet states1))
    send_results = map (\x -> snd (send x)) pss
    pss'         = transpose send_results
  in zipWith (update_io d) pss' states

-- update_io :: Int -> PList (Packet a, Packet a) -> State -> State
update_io :: Int -> PList ((Int, Int, Boolean, Bool, Int, Bool, Int, Int), (Int, Int, Boolean, Bool, Int, Bool, Int, Int)) -> State -> State
update_io d lrps state = 
  let 
    update_is state = setInports state (foldr update_i (inports state) lrps)
    update_os state = if pathDepth state == d
      then setOutports state (zipWith update_o lrps (outports state))
      else state
  in update_os (update_is state)

-- update_o :: (Packet a, Packet a) -> OutPort a -> OutPort a
update_o :: ((Int, Int, Boolean, Bool, Int, Bool, Int, Int), (Int, Int, Boolean, Bool, Int, Bool, Int, Int)) -> (Int, Boolean, Bool, Int, Bool, Int) -> (Int, Boolean, Bool, Int, Bool, Int)
update_o (lp, rp) out = check_left lp (check_right rp out)

check_left (pid, port, pm, pql, pdl, pqr, pdr, e) (p, m, ql, dl, qr, dr) =
  if pqr && pdr > 0 then (p, m, ql, dl, qr, dr) else (p, m, ql, dl, False, dr)
check_right (pid, port, pm, pql, pdl, pqr, pdr, e) (p, m, ql, dl, qr, dr) =
  if pql && pdl > 0 then (p, m, ql, dl, qr, dr) else (p, m, False, dl, qr, dr)

-- update_i :: (Packet a, Packet a) -> PList (InPort a) -> PList (InPort a)
update_i :: ((Int, Int, Boolean, Bool, Int, Bool, Int, Int), (Int, Int, Boolean, Bool, Int, Bool, Int, Int)) -> PList (Int, Int, Boolean) -> PList (Int, Int, Boolean)
update_i (l, r) ins = up_i l (up_i r ins)

-- up_i :: Packet a -> PList (InPort a) -> PList (InPort a)
up_i :: (Int, Int, Boolean, Bool, Int, Bool, Int, Int) -> PList (Int, Int, Boolean) -> PList (Int, Int, Boolean)
up_i (i, p, m', _, _, _, _, _) ins = map (compare_and_update (i, p, m')) ins

-- compare_and_update :: InPort a -> InPort a -> InPort a
compare_and_update :: (Int, Int, Boolean) -> (Int, Int, Boolean) -> (Int, Int, Boolean)
compare_and_update (i, p, m') (pid, port, m) =
  if i==pid && p == port then (pid, port, m') else (pid, port, m)

-- make_packet :: State -> PList (Packet a)
make_packet :: State-> PList (Int, Int, Boolean, Bool, Int, Bool, Int, Int)
make_packet state = map
  (\(p, m, ql, dl, qr, dr) -> (pid state, p, m, ql, dl, qr, dr, 1))
  (outports state)

-- pad_packets :: PList (PList (Packet a)) -> PList (PList (Packet a))
pad_packets :: PList (PList (Int, Int, Boolean, Bool, Int, Bool, Int, Int)) -> PList (PList (Int, Int, Boolean, Bool, Int, Bool, Int, Int))
pad_packets pss = 
  let
    max_ps = maximum (map length pss)
    pad xs = take max_ps (app xs (repeat emptyPacket))
  in map pad pss

-- check_depth :: Int -> State -> State
check_depth :: Int -> State-> State
check_depth d state =
  if pathDepth state == d then state else update_requests False state

-- update_requests :: Bool -> State -> State
update_requests :: Bool -> State-> State
update_requests b state =
  let outports' =
        map (\(p, m, ql, dl, qr, dr) -> (p, m, b, dl, b, dr)) (outports state)
  in  setOutports state outports'

-- simulate_components :: Int -> PList (State) -> PList (State)
simulate_components :: Int -> PList (State) -> PList (State)
simulate_components depth states = map (simulate_component depth) states

-- simulate_component :: Int -> State -> State
simulate_component :: Int -> State-> State
simulate_component d state = 
  let 
    out_signals = map (\(_, _, sig) -> sig) (inports state)
    new_value   = apply_component (compType state) out_signals
  in case new_value of
  Nothing -> state
  Just v  -> if d == pathDepth state then update_outports state v else state

apply_component :: Component -> PList Boolean -> Maybe Boolean
apply_component comp inp = 
  let 
    x = head inp
    y = head (tail inp)
  in 
    case comp of
      Inp  -> Nothing
      Outp -> Just x
      Dff  -> Just x
      Inv  -> Just (inv x)
      And2 -> Just (and2 x y)
      Or2  -> Just (or2 x y)
      Xor  -> Just (xor x y)
    

-- store_inputs :: PList (Label, a) -> State -> State
store_inputs :: PList (Label, Boolean) -> State-> State
store_inputs label_inputs state = if eqC (compType state) Inp
  then head
    (map
      (\((label, input_pid), value) -> update_outports state value)
      (filter (\((label, input_pid), value) -> pid state == input_pid)
              label_inputs
      )
    )
  else state

-- init_dffs :: State -> State
init_dffs :: State -> State
init_dffs state =
  if eqC (compType state) Dff then update_outports state F else state

-- critical_path_depth :: Circuit a -> Int
critical_path_depth :: (Int, PList Label, PList Label, PList (State)) -> Int
critical_path_depth (size, ins, outs, states) = maximum (map pathDepth states)


-- input_values :: Int -> PList (PList a)
bin :: Int -> PList Int
bin n = if n == 0 
      then Nil 
      else 
        let 
          q = n / 2
          r = n - (q * 2)
        in Cons r (bin q)

input_values :: Int -> PList (PList Boolean)
input_values nbits = 
  let 
    int2sig s = if (s == 0) then F else T
    binary n = map int2sig (reverse (take nbits (app (bin n) (repeat 0))))
  in map binary (fromto 0 (2^nbits - 1))
  


-- update_outports :: State -> a -> State
update_outports :: State -> Boolean -> State
update_outports state value = setOutports
  state
  (map (\(p, m, ql, dl, qr, dr) -> (p, value, ql, dl, qr, dr)) (outports state))


-- regs :: Int -> Circuit a
regs :: Int -> (Int, PList Label, PList Label, PList (State))
regs bits = let 
    sto = PS 0 Inp 0 Nil (Cons (0, F, False, 0, True, 8 * (bits - 1) + 5) Nil)
    size = 1 + 7 * bits
    states =
      Cons sto (concat (map (reg 0) (map (\x -> 7*x+1) (fromto 0 (bits-1)))))
    ilabel n pid = (1, pid)
    olabel n pid = (2, pid)
    is = Cons (0,0) (zipWith ilabel (fromto 0 (bits-1)) (map (\x->7*x+1) (fromto 0 (bits-1))))
    os = zipWith olabel (fromto 0 (bits-1)) (map (\x->7*x+7) (fromto 0 (bits-1)))
  in   (size, is, os, states)

reg :: Int -> Int -> PList (State)
reg sto n =
  let reg0, reg1, reg2, reg3, reg4, reg5, reg6, reg7 :: PList (State)
      in1, in2, in3, in4, in5, in6, in7 :: PList (Int, Int, Boolean)
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
      inputs  = take (num_bits + 1) (repeat T)
      cycles  = take num_cycles (repeat inputs)
  in  circuit_simulate cycles example


bench_main :: ()
bench_main = let _ = run 8 1000 in ()

gibbon_main = bench_main
