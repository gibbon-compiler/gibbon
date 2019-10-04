-- Substitution-based lambda calculus benchmark
module LC where

--import Helpers

-- anything thing other than the last constuctor should be in a function call
-- or add a pass that fuse constructors with calls simple
--  F ( K ..) = find the matching case in F and replace it with the code and just put it there..
--q? does it matter what are we traversing?

-- Lambda calculus with inteter arithmetic

data ConstructingCall = KConstruct

data Val = IntV Int
         | LamV IntJ Exp
         | ErrorV
         --  deriving Show

data Exp = LamE IntJ Exp
         | AppE Exp Exp
         | VarE IntJ
         | LitE Int
         | PlusE Exp Exp
         | LetE IntJ Exp Exp
       --    deriving Show

data IntJ = ZeroJ | SuccJ IntJ

data BoolJ = TBool | FBool

isEquel :: IntJ -> IntJ -> BoolJ
isEquel a b =
  case a of
    ZeroJ -> isZero b
    SuccJ a' -> isEquelHelper b  a'

isZero :: IntJ -> BoolJ
isZero a = case a of
    ZeroJ -> TBool
    SuccJ  x -> FBool

isEquelHelper :: IntJ -> IntJ -> BoolJ
isEquelHelper  b a'  =
 case b of
    ZeroJ -> FBool
    SuccJ b' -> isEquel a' b'

data Symbol = A| B| C| D |E |F |G



-- Interpreter

interpExp :: Exp -> Val
interpExp e =
    case e of
      LamE s e -> LamV s e
      AppE e1 e2 -> interpApp (interpExp e1) e2
      VarE s -> ErrorV
      LitE i -> IntV i
      PlusE e1 e2 -> interpPlus  (interpExp e1) e2
      LetE s e1 e2 -> interpExp (substExp e2 s e1 )

interpApp :: Val -> Exp -> Val
interpApp v e2 =
    case v of
      IntV i -> ErrorV
      LamV s e -> interpExp (substExp e s e2 )
      ErrorV -> ErrorV

interpPlus :: Val -> Exp -> Val
interpPlus v e2 =
    case v of
      LamV s e -> ErrorV
      IntV i -> addN (interpExp e2) i
      ErrorV -> ErrorV

substExpHelper1 :: BoolJ -> IntJ -> IntJ-> Exp -> Exp -> Exp
substExpHelper1  b s from e1 to =
  case (b) of
    TBool -> LamE s e1
    FBool -> LamE s (substExp  e1 from to )

substExpHelper2 :: BoolJ -> Exp -> IntJ -> Exp
substExpHelper2 b to s  =
  case (b) of
      TBool -> to
      FBool -> VarE s

substExpHelper3 :: BoolJ -> IntJ -> IntJ -> Exp -> Exp ->Exp->Exp
substExpHelper3 b s from to e1 e2 =
  case (b) of
      TBool-> LetE s (substExp  e1 from to ) e2
      FBool -> LetE s (substExp  e1 from to ) (substExp e2 from to )

substExp :: Exp -> IntJ -> Exp -> Exp
substExp e from to  =
    case e of
      LamE s e1 -> substExpHelper1 (isEquel from s) s from e1 to
      AppE e1 e2 -> AppE (substExp e1 from to ) (substExp e2 from to )
      VarE s -> substExpHelper2 (isEquel from s) to s
      LitE i -> LitE i
      PlusE e1 e2 -> PlusE (substExp e1 from to ) (substExp e2 from to )
      LetE s e1 e2 ->  substExpHelper3  (isEquel from s) s from to e1 e2

addN :: Val ->Int  -> Val
addN v i1  =
    case v of
      LamV s e1 -> ErrorV
      IntV i2 -> IntV (i1 + i2)
      ErrorV -> ErrorV

-- Constant propogation

constProp :: Exp -> Exp
constProp e =
    case e of
      LamE s e1 -> LamE s (constProp e1)
      AppE e1 e2 -> AppE (constProp e1) (constProp e2)
      VarE s -> VarE s
      LitE i -> LitE i
      PlusE e1 e2 -> PlusE (constProp e1) (constProp e2)
      LetE s e1 e2 -> constPropLet  e1 e2 s


createAppE :: ConstructingCall ->  Exp -> Exp -> Exp
createAppE c v1 v2  = case c of
  KConstruct -> AppE v1 v2

createLamE :: ConstructingCall -> IntJ -> Exp -> Exp
createLamE c v1 v2  = case c of
  KConstruct -> LamE v1 v2

constPropLet :: Exp -> Exp -> IntJ-> Exp
constPropLet e1 e2 s  =
    case e1 of
      LamE sl el -> LetE s (createLamE KConstruct sl (constProp el)) (constProp e2)
      AppE ea1 ea2 -> LetE s (createAppE KConstruct (constProp ea1) (constProp ea2)) (constProp e2)
      VarE sv -> substExp  e2 s (VarE sv)
      LitE i -> substExp e2 s (LitE i)
      PlusE e1 e2 -> PlusE (constProp e1) (constProp e2)
      LetE sl el1 el2 -> LetE s (constPropLet  el1 el2 sl) (constProp e2)

-- Partial evaluation of plus
ptExp :: Exp -> Exp
ptExp e =
    case e of
      LamE s e1 -> LamE s (ptExp e1)
      AppE e1 e2 -> AppE (ptExp e1) (ptExp e2)
      VarE s -> VarE s
      LitE i -> LitE i
      PlusE e1 e2 -> ptPlus (ptExp e1) (ptExp e2)
      LetE s e1 e2 -> LetE s (ptExp e1) (ptExp e2)


createVarE :: ConstructingCall -> IntJ -> Exp
createVarE c v1  = case c of
  KConstruct -> VarE v1


createPlusE:: ConstructingCall -> Exp -> Exp->Exp
createPlusE c v1 v2  = case c of
  KConstruct -> PlusE v1 v2

createLetE:: ConstructingCall -> IntJ -> Exp->Exp->Exp
createLetE c v1 v2 v3 = case c of
  KConstruct -> LetE v1 v2 v3


createLitE:: ConstructingCall -> Int ->Exp
createLitE c v1 = case c of
  KConstruct -> LitE v1

ptPlus :: Exp -> Exp -> Exp
ptPlus e1 e2 =
    case e1 of
      LamE sl el1 -> PlusE (createLamE KConstruct  sl el1) e2
      AppE ea1 ea2 -> PlusE (createAppE KConstruct ea1 ea2) e2
      VarE s -> PlusE (createVarE KConstruct  s) e2
      LitE i -> plPlusInner  e2 i
      PlusE ep1 ep2 -> PlusE (createPlusE KConstruct  ep1 ep2) e2
      LetE s el1 el2 -> PlusE (createLetE KConstruct  s el1 el2) e2

plPlusInner ::   Exp ->Int-> Exp
plPlusInner e2 i =
    case e2 of
      LamE sl el1 -> PlusE (createLitE KConstruct i) (LamE sl el1)
      AppE ea1 ea2 -> PlusE (createLitE KConstruct i) (AppE ea1 ea2)
      VarE s -> PlusE (createLitE KConstruct i) (VarE s)
      LitE i2 -> LitE (i + i2)
      PlusE ep1 ep2 -> PlusE (createLitE KConstruct i) (PlusE ep1 ep2)
      LetE s el1 el2 -> PlusE (createLitE KConstruct i) (LetE s el1 el2)

-- Example term
varA :: IntJ
varA =  ZeroJ

varB :: IntJ
varB =  SuccJ varA

varC :: IntJ
varC =  SuccJ varB

varD :: IntJ
varD =  SuccJ varC

varE :: IntJ
varE =  SuccJ varD

varF :: IntJ
varF =  SuccJ varE

ex1 :: Exp
ex1 = (LetE (varA) (LitE 30)
                (LetE (varB) (LamE (varC) (PlusE (LitE 10) (VarE (varC))))
                      (AppE (VarE (varB))
                            (PlusE (VarE (varA)) (LitE 2)))))

buildLargeExp :: Int -> Exp
buildLargeExp n =
  if (n== 0 )
    then
       ex1
    else
      LetE (ZeroJ) ex1 (buildLargeExp (n-1))



eval :: Val -> Int
eval v =
    case v of
      IntV i -> i
      LamV s e -> -1
      ErrorV -> -2


gibbon_main = (eval (interpExp (ptExp (constProp (buildLargeExp 100)))))
--  gibbon_main =  (interpExp (ptExp (constProp (buildLargeExp 100))))

-- main :: IO ()
-- main = do
--   print (eval (interpExp (ptExp (constProp ex1))))
