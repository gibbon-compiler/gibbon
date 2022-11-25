-- https://github.com/ghc/nofib/blob/f34b90b5a6ce46284693119a06d1133908b11856/gc/circsim/Main.lhs
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Use map once" #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use max" #-}
{-# HLINT ignore "Use any" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Redundant if" #-}

#ifdef __GLASGOW_HASKELL__ 
import Prelude hiding (map, concat,head,length,splitAt,zipWith,Just,Nothing,Maybe,repeat,replicate,reverse,take,filter,foldr,foldl,zip,scanl,tail,maximum,or,not,until,(!!),fst,snd,or,any)
import qualified Prelude

to_list :: PList a -> [a]
to_list (Cons a b) = a : to_list b
to_list Nil = []

main :: IO ()
main = print . to_list . map to_list $ run 8 3
sizeParam :: Int
sizeParam = 20 
#endif 

data BinTree a b = Cell a | Node b (BinTree a b) (BinTree a b) deriving (Show)

data Maybe a = Just a | Nothing deriving (Show)

data PList a = Nil | Cons a (PList a) deriving (Show)

data Inport = Inport Int Int Boolean deriving (Show)

data Outport = Outport Int Boolean Bool Int Bool Int deriving (Show)

data Pair a b = Pair a b deriving (Show)

fst :: Pair a b -> a
fst p = case p of Pair x y -> x

snd :: Pair a b -> b
snd p = case p of Pair x y -> y

type Label = Pair Int Int

data State
  = PS
      Int
      -- ^ pid
      Component
      -- ^ compType
      Int
      -- ^ pathDepth
      (PList Inport)
      -- ^ inports
      (PList Outport)
      -- ^ outports
  deriving (Show)

data Circuit
  = Circuit
      Int
      -- ^ Size
      (PList Label)
      -- ^ Input locations
      (PList Label)
      -- ^ Output locations
      (PList State)

transpose :: PList (PList a) -> PList (PList a)
transpose a = case a of
  Nil -> Nil
  Cons aa bb -> case aa of
    Nil -> Nil
    Cons _a _b -> Cons (map head a) (transpose (map tail a))

zip :: PList a -> PList b -> PList (Pair a b)
zip as bs =
  case as of
    Nil -> Nil
    Cons z zs -> case bs of
      Nil -> Nil
      Cons y ys -> Cons (Pair z y) (zip zs ys)

not :: Bool -> Bool
not a = if a then False else True

maximum :: PList Int -> Int
maximum a =
  case a of
    Nil -> 0
    Cons z zs -> let m = maximum zs in max z m

foldr :: (a -> b -> b) -> b -> PList a -> b
foldr f z a =
  case a of
    Nil -> z
    Cons z1 zs -> f z1 (foldr f z zs)

or :: PList Bool -> Bool
or a = case a of
  Nil -> False
  Cons z zs -> z || or zs -- codegen generates RHS first

scanl :: (b -> a -> b) -> b -> PList a -> PList b
scanl f z as =
  case as of
    Nil -> Cons z Nil
    Cons a as' -> Cons z (scanl f (f z a) as')

tail :: PList a -> PList a
tail a = case a of
  Nil -> Nil
  Cons z zs -> zs

foldl :: (b -> a -> b) -> b -> PList a -> b
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
    else case a of
      Nil -> Nil
      Cons z zs -> Cons z (take (n - 1) zs)

length :: PList a -> Int
length a = case a of
  Nil -> 0
  Cons x xs -> 1 + length xs

head :: PList a -> a
head a = case a of
  Cons x xs -> x

replicate :: Int -> a -> PList a
replicate n x = if n <= 0 then Nil else Cons x (replicate (n - 1) x)

reverse_go :: PList a -> PList a -> PList a
reverse_go b acc =
  case b of
    Nil -> acc
    Cons z zs -> reverse_go zs (Cons z acc)

reverse :: PList a -> PList a
reverse a = reverse_go a Nil

app :: PList a -> PList a -> PList a
app a b = case a of
  Nil -> b
  Cons x xs -> Cons x (app xs b)

splitAt :: Int -> PList a -> Pair (PList a) (PList a)
splitAt n a =
  if n == 0
    then Pair Nil a
    else case a of
      Nil -> Pair Nil Nil -- error case
      Cons x xs -> case splitAt (n - 1) xs of Pair c d -> Pair (Cons x c) d

map :: (a -> b) -> PList a -> PList b
map f a = case a of
  Nil -> Nil
  Cons x xs -> Cons (f x) (map f xs)

until :: (a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x then x else until p f (f x)

concat :: PList (PList a) -> PList a
concat as = case as of
  Nil -> Nil
  Cons x xs -> let y = concat xs in app x y

zipWith :: (a -> b -> c) -> PList a -> PList b -> PList c
zipWith f as bs = case as of
  Nil -> Nil
  Cons x xs -> case bs of
    Nil -> Nil
    Cons y ys -> Cons (f x y) (zipWith f xs ys)

fromto :: Int -> Int -> PList Int
fromto a b = if a > b then Nil else Cons a (fromto (a + 1) b)

put :: PList a -> BinTree a ()
put xs =
  if length xs == 1
    then Cell (head xs)
    else case splitAt (div (length xs) 2) xs of Pair fstHalf sndHalf -> Node () (put fstHalf) (put sndHalf)

get :: BinTree a b -> PList a
get tree = case tree of
  Cell x -> Cons x Nil
  Node x l r -> app (get l) (get r)

upsweep :: (a -> a -> a) -> BinTree a b -> Pair a (BinTree a (Pair a a))
upsweep f tree = case tree of
  Cell a -> Pair a (Cell a)
  Node x l r ->
    case upsweep f l of
      Pair lv l' -> case upsweep f r of
        Pair rv r' -> Pair (f lv rv) (Node (Pair lv rv) l' r')

downsweep :: (a -> b -> c -> Pair c c) -> c -> BinTree d (Pair a b) -> BinTree c ()
downsweep g d tree = case tree of
  Cell x -> Cell d
  Node lrv l r ->
    case lrv of
      Pair lv rv ->
        case g lv rv d of
          Pair dl dr ->
            let l' = downsweep g dl l
                r' = downsweep g dr r
             in Node () l' r'

sweep_ud ::
  (a -> a -> a) ->
  (a -> a -> b -> Pair b b) ->
  b ->
  BinTree a c ->
  Pair a (BinTree b ())
sweep_ud up down u t =
  case upsweep up t of
    Pair ans t' -> Pair ans (downsweep down u t')

scanL :: (a -> a -> a) -> a -> PList a -> Pair a (PList a)
scanL f u xs =
  let down l r x = Pair x (f x l)
   in case sweep_ud f down u (put xs) of
        Pair up_ans t' -> Pair up_ans (get t')

scanR :: (a -> a -> a) -> a -> PList a -> Pair a (PList a)
scanR f u xs =
  let down l r x = Pair (f r x) x
   in case sweep_ud f down u (put xs) of
        Pair up_ans t' -> Pair up_ans (get t')

scanlr ::
  (a -> a -> a) -> (a -> a -> a) -> a -> a -> PList a -> Pair (Pair a a) (PList (Pair a a))
scanlr f g lu ru xs =
  let up p1 p2 = case p1 of Pair lx ly -> case p2 of Pair rx ry -> Pair (f lx rx) (g ly ry)
      down p1 p2 p3 = case p1 of Pair lx ly -> case p2 of Pair rx ry -> case p3 of Pair a b -> Pair (Pair a (g ry b)) (Pair (f a lx) b)
      xs' = map (\x -> Pair x x) xs
   in case sweep_ud up down (Pair lu ru) (put xs') of
        Pair v1 t -> case v1 of
          Pair l_ans r_ans ->
            let ans = Pair (g r_ans ru) (f lu l_ans)
             in Pair ans (get t)

data Component
  = None -- no component
  | Inp -- input to the entire circuit
  | Outp -- output from the entire circuit
  | Dff -- delay flip flop
  | Inv -- inverter
  | And2 -- 2-input and gate
  | Or2 -- 2-input or gate
  | Xor -- exclusive or gate
  deriving (Show)

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

pid :: State -> Int
pid st = case st of
  PS pid _ _ _ _ -> pid

compType :: State -> Component
compType st = case st of
  PS _ compType _ _ _ -> compType

pathDepth :: State -> Int
pathDepth st = case st of
  PS _ _ pathDepth _ _ -> pathDepth

inports :: State -> PList Inport
inports st = case st of
  PS _ _ _ inports _ -> inports

outports :: State -> PList Outport
outports st = case st of
  PS _ _ _ _ outports -> outports

setInports :: State -> PList Inport -> State
setInports st i = case st of
  PS pid ct pd _ o -> PS pid ct pd i o

setOutports :: State -> PList Outport -> State
setOutports st o = case st of
  PS pid ct pd i _ -> PS pid ct pd i o

nearest_power_of_two :: Int -> Int
nearest_power_of_two x = until (\y -> y >= x) (\y -> y * 2) 1

pad_circuit :: Circuit -> Circuit
pad_circuit c1 = case c1 of
  Circuit size ins outs states ->
    let p2 = nearest_power_of_two size
     in Circuit p2 ins outs (app states (replicate (p2 - length states) emptyState))

emptyState :: State
emptyState = PS (-1) None (-1) Nil Nil

data Boolean = F | T deriving (Show)

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
and2 x y = if eq x T && eq y T then T else F

or2 :: Boolean -> Boolean -> Boolean
or2 x y = if eq x T || eq y T then T else F

xor :: Boolean -> Boolean -> Boolean
xor x y = if eq x y then T else F

data Packet
  = Packet
      Int
      -- ^ ID
      Int
      -- ^ Output Port #
      Boolean
      -- ^ Signal Value
      Bool
      -- ^ Send to Left?
      Int
      -- ^ Distance to Left
      Bool
      -- ^ Send to Right?
      Int
      -- ^ Distance to Right?
      Int
      -- ^ Extent

emptyPacket :: Packet
emptyPacket = Packet (-1) (-1) F False 0 False 0 1

send_right :: Packet -> Packet -> Packet
send_right p1 p2 = case p1 of
  Packet ia sa ma qla dla qra dra ea -> case p2 of
    Packet ib sb mb qlb dlb qrb drb eb ->
      if qra && dra > eb
        then Packet ia sa ma qla dla qra (dra - eb) (ea + eb)
        else Packet ib sb mb qlb dlb qrb drb (ea + eb)

send_left :: Packet -> Packet -> Packet
send_left p1 p2 = case p1 of
  Packet ia sa ma qla dla qra dra ea -> case p2 of
    Packet ib sb mb qlb dlb qrb drb eb ->
      if qlb && dlb > ea
        then Packet ib sb mb qlb (dlb - ea) qrb drb (ea + eb)
        else Packet ia sa ma qla dla qra dra (ea + eb)

send :: PList Packet -> Pair (Pair Packet Packet) (PList (Pair Packet Packet))
send = scanlr send_right send_left emptyPacket emptyPacket

circuit_simulate :: PList (PList Boolean) -> Circuit -> PList (PList Boolean)
circuit_simulate inputs_list circuit = map collect_outputs (simulate inputs_list circuit)

collect_outputs :: Circuit -> PList Boolean
collect_outputs c1 = case c1 of
  Circuit size ins outs states ->
    let -- get_output (Pair (label) (p))
        -- 		 = third (head [ head (inports s) | s<-states, p==pid s])
        third i1 = case i1 of Inport _ _ v -> v
        get_first_inport s = head (inports s)
        get_output :: Pair Int Int -> Boolean
        get_output p = case p of
          Pair label p ->
            let is_req_pid s = pid s == p
             in third (head (map get_first_inport (filter is_req_pid states)))
     in map get_output outs

simulate :: PList (PList Boolean) -> Circuit -> PList Circuit
simulate inputs_list c1 = case c1 of
  Circuit size ins outs states ->
    let circuit = Circuit size ins outs states
        circuit' = Circuit size ins outs (map init_dffs states)
        cpd = critical_path_depth circuit
     in tail (scanl (do_cycle cpd) circuit' inputs_list)

do_cycle :: Int -> Circuit -> PList Boolean -> Circuit
do_cycle cpd c1 inputs = case c1 of
  Circuit size ins outs states ->
    let states1 = map (store_inputs (zip ins inputs)) states
        states2 = do_sends 0 states1
        sim_then_send state d = do_sends d (simulate_components d state)
        states3 = foldl sim_then_send states2 (fromto 1 cpd)
        states4 = restore_requests states states3
     in Circuit size ins outs states4

restore_outport :: Outport -> Outport -> Outport
restore_outport o1 o2 = case o1 of
  Outport p _ ql dl qr dq -> case o2 of
    Outport _ m _ _ _ _ -> Outport p m ql dl qr dq

restore :: State -> State -> State
restore os ns =
  setOutports ns (zipWith restore_outport (outports os) (outports ns))

restore_requests :: PList State -> PList State -> PList State
restore_requests old_states new_states = zipWith restore old_states new_states

do_sends :: Int -> PList State -> PList State
do_sends d = until (acknowledge d) (do_send d)

check_lr_requests :: Outport -> Bool
check_lr_requests o1 = case o1 of Outport p m ql dl qr dr -> ql || qr

check_requests :: PList Outport -> Bool
check_requests xs = or (map check_lr_requests xs)

acknowledge :: Int -> PList State -> Bool
acknowledge d states =
  let states1 = map (check_depth d) states
   in not (or (map (\x -> check_requests (outports x)) states1))

do_send :: Int -> PList State -> PList State
do_send d states =
  let states1 = map (check_depth d) states
      pss = transpose (pad_packets (map make_packet states1))
      send_results = map (\x -> snd (send x)) pss
      pss' = transpose send_results
   in zipWith (update_io d) pss' states

update_io :: Int -> PList (Pair Packet Packet) -> State -> State
update_io d lrps state =
  let update_is state = setInports state (foldr update_i (inports state) lrps)
      update_os state =
        if pathDepth state == d
          then setOutports state (zipWith update_o lrps (outports state))
          else state
   in update_os (update_is state)

update_o :: Pair Packet Packet -> Outport -> Outport
update_o p out = case p of Pair lp rp -> check_left lp (check_right rp out)

check_left :: Packet -> Outport -> Outport
check_left p1 o1 = case p1 of
  Packet pid port pm pql pdl pqr pdr e -> case o1 of
    Outport p m ql dl qr dr -> if pqr && pdr > 0 then Outport p m ql dl qr dr else Outport p m ql dl False dr

check_right :: Packet -> Outport -> Outport
check_right p1 o1 = case p1 of
  Packet pid port pm pql pdl pqr pdr e -> case o1 of
    Outport p m ql dl qr dr ->
      if pql && pdl > 0 then Outport p m ql dl qr dr else Outport p m False dl qr dr

update_i :: Pair Packet Packet -> PList Inport -> PList Inport
update_i p1 ins = case p1 of Pair l r -> up_i l (up_i r ins)

up_i :: Packet -> PList Inport -> PList Inport
up_i p1 = case p1 of Packet i p m' _ _ _ _ _ -> map (compare_and_update (Inport i p m'))

compare_and_update :: Inport -> Inport -> Inport
compare_and_update i1 i2 = case i1 of
  Inport i p m' -> case i2 of
    Inport pid port m ->
      if i == pid && p == port
        then Inport pid port m'
        else Inport pid port m

make_packet :: State -> PList Packet
make_packet state =
  map
    (\o1 -> case o1 of Outport p m ql dl qr dr -> Packet (pid state) p m ql dl qr dr 1)
    (outports state)

pad :: Int -> PList Packet -> PList Packet
pad max_ps xs = app xs (replicate (max_ps - length xs) emptyPacket)

pad_packets :: PList (PList Packet) -> PList (PList Packet)
pad_packets pss =
  let max_ps = maximum (map length pss)
   in map (pad max_ps) pss

check_depth :: Int -> State -> State
check_depth d state =
  if pathDepth state == d then state else update_requests False state

update_requests :: Bool -> State -> State
update_requests b state =
  let outports' =
        map (\o1 -> case o1 of Outport p m ql dl qr dr -> Outport p m b dl b dr) (outports state)
   in setOutports state outports'

simulate_components :: Int -> PList State -> PList State
simulate_components depth = map (simulate_component depth)

simulate_component :: Int -> State -> State
simulate_component d state =
  if d == pathDepth state
    then
      let out_signals = map (\i1 -> case i1 of Inport _ _ sig -> sig) (inports state)
          new_value = apply_component (compType state) out_signals
       in case new_value of
            Nothing -> state
            Just v -> update_outports state v
    else state

apply_component :: Component -> PList Boolean -> Maybe Boolean
apply_component comp inp =
  case comp of
    Inp -> Nothing
    Outp -> case inp of
      Cons x _xs -> Just x
    Dff -> case inp of
      Cons x _xs -> Just x
    Inv -> case inp of
      Cons x _xs -> Just (inv x)
    And2 -> case inp of
      Cons x xs ->
        case xs of
          Cons y ys -> Just (and2 x y)
    Or2 -> case inp of
      Cons x xs ->
        case xs of
          Cons y ys -> Just (or2 x y)
    Xor -> case inp of
      Cons x xs ->
        case xs of
          Cons y ys -> Just (xor x y)

store_inputs :: PList (Pair Label Boolean) -> State -> State
store_inputs label_inputs state =
  if eqC (compType state) Inp
    then
      head
        ( map
            (\p1 -> case p1 of Pair p2 value -> case p2 of Pair label input_pid -> update_outports state value)
            ( filter
                (\p1 -> case p1 of Pair p2 value -> case p2 of Pair label input_pid -> pid state == input_pid)
                label_inputs
            )
        )
    else state

init_dffs :: State -> State
init_dffs state =
  if eqC (compType state) Dff then update_outports state F else state

critical_path_depth :: Circuit -> Int
critical_path_depth c1 = case c1 of Circuit size ins outs states -> maximum (map pathDepth states)

bin :: Int -> PList Int
bin n =
  if n == 0
    then Nil
    else
      let q = div n 2
          r = n - q * 2
       in Cons r (bin q)

int2sig :: Int -> Boolean
int2sig s = if s == 0 then F else T

binary :: Int -> Int -> PList Boolean
binary nbits n =
  let temp = bin n
   in map int2sig (reverse (app temp (replicate (nbits - length temp) 0)))

input_values :: Int -> PList (PList Boolean)
input_values nbits = map (binary nbits) (fromto 0 (2 ^ nbits - 1))

update_outports :: State -> Boolean -> State
update_outports state value =
  setOutports
    state
    (map (\o1 -> case o1 of Outport p m ql dl qr dr -> Outport p value ql dl qr dr) (outports state))

regs :: Int -> Circuit
regs bits =
  let ilabel n pid = Pair 1 pid
      olabel n pid = Pair 2 pid
      sto = PS 0 Inp 0 Nil (Cons (Outport 0 F False 0 True (8 * (bits - 1) + 5)) Nil)
      size = 1 + 7 * bits
      states =
        Cons sto (concat (map (reg 0) (map (\x -> 7 * x + 1) (fromto 0 (bits - 1)))))
      is = Cons (Pair 0 0) (zipWith ilabel (fromto 0 (bits - 1)) (map (\x -> 7 * x + 1) (fromto 0 (bits - 1))))
      os = zipWith olabel (fromto 0 (bits - 1)) (map (\x -> 7 * x + 7) (fromto 0 (bits - 1)))
   in Circuit size is os states

reg :: Int -> Int -> PList State
reg sto n =
  let reg1, reg2, reg3, reg4, reg5, reg6, reg7 :: State
      in1, in2, in3, in4, in5, in6, in7 :: PList Inport
      out1, out2, out3, out4, out5, out6, out7 :: PList Outport

      in1 = Nil
      out1 = Cons (Outport 0 F False 0 True 4) Nil
      reg1 = PS n Inp 0 in1 out1

      in2 = Cons (Inport (n + 5) 0 F) Nil
      out2 = Cons (Outport 0 F False 0 True 5) Nil
      reg2 = PS (n + 1) Dff 1 in2 out2

      in3 = Cons (Inport sto 0 F) Nil
      out3 = Cons (Outport 0 F False 0 True 1) Nil
      reg3 = PS (n + 2) Inv 1 in3 out3

      in4 = Cons (Inport (n + 1) 0 F) (Cons (Inport (n + 2) 0 F) Nil)
      out4 = Cons (Outport 0 F False 0 True 2) Nil
      reg4 = PS (n + 3) And2 2 in4 out4

      in5 = Cons (Inport sto 0 F) (Cons (Inport n 0 F) Nil)
      out5 = Cons (Outport 0 F False 0 True 1) Nil
      reg5 = PS (n + 4) And2 1 in5 out5

      in6 = Cons (Inport (n + 3) 0 F) (Cons (Inport (n + 4) 0 F) Nil)
      out6 = Cons (Outport 0 F True 4 False 0) Nil
      reg6 = PS (n + 5) Or2 3 in6 out6

      in7 = Cons (Inport (n + 1) 0 F) Nil
      out7 = Nil
      reg7 = PS (n + 6) Outp 4 in7 out7
   in Cons reg1 (Cons reg2 (Cons reg3 (Cons reg4 (Cons reg5 (Cons reg6 (Cons reg7 Nil))))))

run :: Int -> Int -> PList (PList Boolean)
run num_bits num_cycles =
  let example = pad_circuit (regs num_bits)
      inputs = replicate (num_bits + 1) T
      cycles = replicate num_cycles inputs
   in circuit_simulate cycles example

gibbon_main =
  let m = sizeParam
      n = sizeParam
      _ = run m n
   in ()