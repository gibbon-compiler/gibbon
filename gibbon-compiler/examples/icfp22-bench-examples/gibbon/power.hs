-- source: https://github.com/ghc/nofib/blob/f34b90b5a6ce46284693119a06d1133908b11856/gc/power/Main.hs

data Ps a = Pz | OpP a (Ps a)
data PList a = Nil | Cons a (PList a) 

tree :: Ps Int
forest :: Ps Int
list :: Ps Int
ts :: Ps Int

dot :: a -> Ps a -> Ps a
dot c b = case b of 
    Pz -> Pz 
    OpP f fs -> OpP (c*f) (dot c fs)

x:: Ps a
x = OpP 0 (OpP 1 Pz)

psNeg :: Ps a -> Ps a 
psNeg a = case a of 
    Pz -> Pz 
    OpP f fs -> OpP (-f) (psNeg fs)

psAdd :: Ps a -> Ps a -> Ps a 
psAdd a b = case a of 
    Pz -> b
    OpP f fs -> case b of 
        Pz -> a 
        OpP g gs -> OpP (f + g) (psAdd fs gs)

psMult :: Ps a -> Ps a -> Ps a
psMult a b = 
    case a of 
        Pz -> Pz 
        OpP f fs -> case b of 
                    Pz -> Pz 
                    OpP g gs -> OpP (f*g) (psAdd (dot f gs) (psAdd (dot g fs) (psMult x (psMult fs gs))))

psDiv :: Ps a -> Ps a -> Ps a
psDiv a b = 
    case a of 
        Pz -> case b of 
                Pz -> error
                OpP g gs -> if g ==0 then psDiv Pz gs else Pz
        OpP f fs -> if f ==0 && g == 0
                then psDiv fs gs 
                else let q = f/g in OpP q (psDiv (psAdd fs (psNeg (dot q gs))) b)



tree   = OpP 0 forest
forest = compose list tree
list   = OpP 1 list
ts = OpP 1 (psMult ts ts)

extract :: Int -> Ps a -> PList a
extract n ps = 
    if n == 0 
        then Nil 
        else case ps of 
            Pz -> Nil
            OpP x ps -> Cons x (extract (n-1) ps)


deriv:: Ps a -> Ps a
integral:: Ps a -> Ps a
compose:: Ps a -> Ps a -> Ps a
revert:: Ps a -> Ps a
takePs:: Int -> Ps a -> PList a
expx, sinx, cosx:: Ps a

takePs n fs = if n == 0 then Pz else case fs of 
    Pz -> Pz 
    OpP f fs -> OpP f (take (n-1) fs)

compose a b = 
    case a of 
        Pz -> Pz 
        OpP f fs -> case b of 
            Pz -> OpP f Pz
            OpP g gs -> if g ==0 
                then OpP f (psMult gs (compose fs (OpP 0 gs)))
                else psAdd (OpP f Pz) (psMult b (compose fs b))

revert a = case a of 
    Pz -> error 
    OpP f fs -> if f == 0
        then let rs = OpP 0 (psDiv 1 (compose fs rs)) in rs
        else error

deriv a = case a of 
    Pz -> Pz 
    OpP f fs -> deriv1 fs 1 
    where 
        deriv1 a n = case a of 
            Pz -> Pz 
            OpP f fs -> OpP (n*f) (deriv1 fs (n+1))

integral fs = OpP 0 (int1 fs 1)
    where 
        int1 a n = case a of 
            Pz -> Pz 
            OpP f fs -> OpP (f/n) (int1 fs (n+1))

sqrt a = case a of 
    Pz -> Pz 
    OpP f fs -> if f == 1 
        then let qs = 1 + integral (psDiv (OpP 1 fs) (dot 2 qs)) in qs
        else case fs of 
            Pz -> error 
            OpP f' fs' -> if f' == 0 then OpP 0 (sqrt fs') else error

expx = 1 + (integral expx)
sinx = integral cosx 
cosx = 1 - (integral sinx)

gibbon_main = 
    let 
        n = sizeParam
        _ = extract p (sinx - sqrt (1-cosx^2)) 
        _ = extract p (sinx/cosx - revert (integral (1/(1+x^2))))
        _ = extract p ts 
        _ = extract p tree
    in ()  

-- TODO fix and test