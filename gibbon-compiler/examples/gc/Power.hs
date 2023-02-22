-- source: https://github.com/ghc/nofib/blob/f34b90b5a6ce46284693119a06d1133908b11856/gc/power/Main.hs
module Power where

import Gibbon.Prelude

--------------------------------------------------------------------------------

data Ps = Pz | OpP Float Ps | Error -- powerseries = zero | a + x * powerseries
data PList1 = Nil1 | Cons1 Float PList1 | ErrorL deriving Show

size :: PList1 -> Int
size ls =
  case ls of
    Nil1 -> 0
    Cons1 _x xs -> 1 + size xs
    ErrorL -> -1

pone :: Ps
pone = OpP 1.0 Pz -- 1 = 1 + x * (0)

dot :: Float -> Ps -> Ps
dot c b = case b of
    Pz -> Pz
    OpP f fs -> OpP (c .*. f) (dot c fs)
    Error -> Error

psX :: Ps
psX = OpP 0.0 (OpP 1.0 Pz)

psNeg :: Ps -> Ps
psNeg a = case a of
    Pz -> Pz
    OpP f fs -> OpP (0.0 .-. f) (psNeg fs)
    Error -> Error

psAdd :: Ps -> Ps -> Ps
psAdd a b = case a of
    Pz -> b
    OpP f fs -> case b of
        Pz -> a
        OpP g gs -> OpP (f .+. g) (psAdd fs gs)
        Error -> Error
    Error -> Error

psMult :: Ps -> Ps -> Ps
psMult a b =
    case a of
        Pz -> Pz
        OpP f fs -> case b of
                    Pz -> Pz
                    OpP g gs -> OpP (f.*.g) (psAdd (dot f gs) (psAdd (dot g fs) (psMult psX (psMult fs gs))))
                    Error -> Error
        Error -> Error

psDiv :: Int -> Ps -> Ps -> Ps
psDiv n a b =
    if n == 0 then Pz else
    case a of
        Pz -> case b of
                Pz -> Error
                OpP g gs -> if g .==. 0.0 then psDiv n Pz gs else Pz
                Error -> Error
        OpP f fs -> case b of
                Pz -> Error
                OpP g gs ->
                    if f .==. 0.0 && g .==. 0.0
                        then psDiv n fs gs
                        else let q = f./.g in OpP q (psDiv (n-1) (psAdd fs (psNeg (dot q gs))) b)
                Error -> Error
        Error -> Error

takePs :: Int -> Ps -> Ps
takePs n fs = if n == 0 then Pz else case fs of
    Pz -> Pz
    OpP f fs' -> OpP f (takePs (n-1) fs')
    Error -> Error

list, ts :: Int -> Ps
-- tree, forest :: Ps
-- tree   = OpP 0.0 forest
-- forest = compose list tree
list n = if n == 0 then Pz else OpP 1.0 (list (n-1))
ts n = if n == 0 then Pz else OpP 1.0 (takePs (n-1) (psMult (ts (n-1)) (ts (n-1))))

compose:: Ps -> Ps -> Ps
-- (1+x)^2
compose a b =
    case a of
        Pz -> Pz
        OpP f fs -> case b of
            Pz -> OpP f Pz
            OpP g gs -> if g .==. 0.0
                then OpP f (psMult gs (compose fs (OpP 0.0 gs)))
                else psAdd (OpP f Pz) (psMult b (compose fs b))
            Error -> Error
        Error -> Error

getRs :: Int -> Ps -> Ps
getRs n fs = if n == 0 then Pz else OpP 0.0 (psDiv (n-1) pone (compose fs (getRs (n-1) fs)))

revert :: Int -> Ps -> Ps
-- y = 2 + 3x => x = (2-y)/3 = 2/3 - 1/3y
revert n a = case a of
    Pz -> Error
    OpP f fs -> if f .==. 0.0
        then getRs n fs
        else case fs of
            OpP f' fs' -> case fs' of
                Pz -> OpP (f./.f') (OpP (0.0 .-.1.0 ./. f') Pz)

deriv1 :: Ps -> Int -> Ps
deriv1 a n = case a of
    Pz -> Pz
    OpP f fs -> OpP ((intToFloat n) .*. f) (deriv1 fs (n+1))
    Error -> Error


deriv :: Ps -> Ps
deriv a = case a of
    Pz -> Pz
    OpP f fs -> deriv1 fs 1
    Error -> Error

int1 :: Ps -> Int -> Ps
int1 a n = case a of
    Pz -> Pz
    OpP f fs -> OpP (f./. (intToFloat n)) (int1 fs (n+1))
    Error -> Error

integral :: Ps -> Ps
integral fs = OpP 0.0 (int1 fs 1)


getQs :: Int -> Ps -> Ps
getQs n fs = if n <= 0 then Pz else psAdd pone (integral (psDiv (n - 1) (deriv (OpP 1.0 fs)) (dot 2.0 (getQs (n-1) fs))))

psSqrt :: Int -> Ps -> Ps
-- sqrt (1-x) = 1 - x/2 - x^2/8 - x^3/16 - (5 x^4)/128 + O[x]^5
psSqrt n a = case a of
    Pz -> Pz
    OpP f fs -> if f .==. 1.0
        then getQs n fs
        else case fs of
            Pz -> Error
            OpP f' fs' -> if f' .==. 0.0 then OpP 0.0 (psSqrt (n-1) fs') else Error
            Error -> Error
    Error -> Error

expx, sinx, cosx:: Int -> Ps
-- exp(X) = 1 + X + X^2/2 + X^3/6 + X^4/24 + O[X]^5
expx n = if n == 0 then Pz else psAdd pone (integral (expx (n-1))) -- 1 + integral expx

-- sin(X) = X - X^3/6 + X^5/120 - X^7/5040 + O[X]^8
sinx n = if n == 0 then Pz else integral (cosx (n-1))

-- cos(X) = 1 - X^2/2 + X^4/24 - X^6/720 + O[X]^7
cosx n = if n == 0 then Pz else psAdd pone (psNeg (integral (sinx (n-1)))) -- 1 - integral sinx

equal :: PList1 -> PList1 -> Bool
equal as bs =
    case as of
        ErrorL -> case bs of
          Nil1 -> False
          Cons1 x pl -> False
          ErrorL -> True
        Nil1 -> case bs of
            Nil1 -> True
            Cons1 _ _ -> False
            ErrorL -> False
        Cons1 a as' -> case bs of
            Nil1 -> False
            Cons1 b bs' -> let d = (a .-. b)
                          in ((0.0 .-. 1e-7) .<. d) && (d .<. 1e-7) && equal as' bs'
            ErrorL -> False

toList :: Ps -> PList1
toList ps = case ps of
    Pz -> Nil1
    OpP x ps' -> Cons1 x (toList ps')


-- * NOTE: checking as many terms as possible without loss of precision using floating value
psB, psC :: Int -> Ps
expx_ans, sinx_ans, cosx_ans, ansb, ansc, ansd :: PList1

expx_ans = Cons1 1.0 ( Cons1 1.0 ( Cons1 (1.0./.2.0) ( Cons1 (1.0./.6.0) ( Cons1 (1.0./.24.0) ( Cons1 (1.0./.120.0) ( Cons1 (1.0./.720.0) ( Cons1 (1.0./.5040.0) ( Cons1 (1.0./.40320.0) Nil1 ))))))))
-- 1.0 + 1.0x^1 + 0.5x^2 + 0.16666667x^3 + 4.1666668e-2x^4 + 8.333334e-3x^5 + 1.3888889e-3x^6 + 1.984127e-4x^7 + 2.4801588e-5x^8 + 0
-- expx = 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + O[x]^9

sinx_ans = Cons1 0.0 ( Cons1 1.0 ( Cons1 0.0 ( Cons1 (0.0 .-. 1.0./.6.0) ( Cons1 0.0 ( Cons1 (1.0./.120.0) ( Cons1 0.0 ( Cons1 (0.0.-.1.0./.5040.0) ( Cons1 0.0 ( Cons1 (1.0./.362880.0) ( Cons1 0.0 Nil1))))))))))
-- 0.0 + 1.0x^1 + 0.0x^2 + -0.16666667x^3 + 0.0x^4 + 8.333334e-3x^5 + 0.0x^6 + -1.984127e-4x^7 + 0.0x^8 + 2.7557319e-6x^9 + 0.0x^10 + 0
-- sinx = x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 + O[x]^11

cosx_ans = Cons1 1.0 ( Cons1 0.0 ( Cons1 (0.0.-.1.0./.2.0) ( Cons1 0.0 ( Cons1 (1.0./.24.0) ( Cons1 0.0 ( Cons1 (0.0.-.1.0./.720.0) ( Cons1 0.0 ( Cons1 (1.0./.40320.0) Nil1 ))))))))
-- sinx - sqrt (1-cosx^2) = 0


psB n = psAdd (sinx n) (psNeg (psSqrt n (psAdd pone (psNeg (psMult (cosx n) (cosx n))))))
ansb = Cons1 0.0 (
        Cons1 0.0 (
            Cons1 0.0 (
                Cons1 0.0 (
                    Cons1 0.0 Nil1 ))))

-- sinx - sqrt(1-cosx^2) = sinx - sinx = 0

psC n = psAdd (psDiv n (sinx n) (cosx n)) (psNeg (revert n (integral (psDiv n pone (psAdd pone (psMult psX psX))))))
ansc = Cons1 0.0 (
        Cons1 0.0 (
            Cons1 0.0 (
                Cons1 0.0 (
                    Cons1 0.0 Nil1 ))))

-- sinx/tanx - revert(integral 1/(1+x^2)) = tanx - revert(atanx) = 0

ansd = Cons1 1.0 (Cons1 1.0 (Cons1 2.0 (Cons1 5.0 (Cons1 14.0 (Cons1 42.0 (Cons1 132.0 (Cons1 429.0 (Cons1 1430.0 (Cons1 4862.0 (Cons1 16796.0 (Cons1 58786.0 Nil1)))))))))))

-----------------------------------------------------------------------------------------

bench_ts :: ()
bench_ts =
  let ps = iterate (ts 20)
      sz = size (toList ps)
  in print_check (sz == 20)

bench_psb :: ()
bench_psb =
  let ps = iterate (psB 50)
      sz = size (toList ps)
  in print_check (sz == 90)

bench_psc :: ()
bench_psc =
  let ps = iterate (psC 5)
      sz = size (toList ps)
  in print_check (sz == 5)

gibbon_main =
  if eqBenchProg "ts"
  then bench_ts
  else if eqBenchProg "psb"
  then bench_psb
  else if eqBenchProg "psc"
  then bench_psc
  else let _ = printsym (quote "benchrunner: select benchmark to run with --bench-prog\n")
       in ()
