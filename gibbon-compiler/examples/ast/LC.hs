-- Substitution-based lambda calculus benchmark
module LC where

import Helpers


-- Lambda calculus with inteter arithmetic

data Val = IntV Int
         | LamV Sym Exp
         | ErrorV
           deriving Show

data Exp = LamE Sym Exp
         | AppE Exp Exp
         | VarE Sym
         | LitE Int
         | PlusE Exp Exp
         | LetE Sym Exp Exp
           deriving Show

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

substExp :: Exp -> Sym -> Exp -> Exp
substExp e from to  =
    case e of
      LamE s e1 ->
          if eqsym from s
          then LamE s e1
          else LamE s (substExp  e1 from to )
      AppE e1 e2 -> AppE (substExp e1 from to ) (substExp e2 from to )
      VarE s -> if eqsym from s
                then to
                else VarE s
      LitE i -> LitE i
      PlusE e1 e2 -> PlusE (substExp e1 from to ) (substExp e2 from to )
      LetE s e1 e2 -> if eqsym from s
                      then LetE s (substExp  e1 from to ) e2
                      else LetE s (substExp  e1 from to ) (substExp e2 from to )

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
      LetE s e1 e2 -> constPropLet s e1 e2

constPropLet :: Sym -> Exp -> Exp -> Exp
constPropLet s e1 e2 =
    case e1 of
      LamE sl el -> LetE s (LamE sl (constProp el)) (constProp e2)
      AppE ea1 ea2 -> LetE s (AppE (constProp ea1) (constProp ea2)) (constProp e2)
      VarE sv -> substExp  e2 s (VarE sv)
      LitE i -> substExp e2 s (LitE i)
      PlusE e1 e2 -> PlusE (constProp e1) (constProp e2)
      LetE sl el1 el2 -> LetE s (constPropLet sl el1 el2) (constProp e2)

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

ptPlus :: Exp -> Exp -> Exp
ptPlus e1 e2 =
    case e1 of
      LamE sl el1 -> PlusE (LamE sl el1) e2
      AppE ea1 ea2 -> PlusE (AppE ea1 ea2) e2
      VarE s -> PlusE (VarE s) e2
      LitE i -> plPlusInner i e2
      PlusE ep1 ep2 -> PlusE (PlusE ep1 ep2) e2
      LetE s el1 el2 -> PlusE (LetE s el1 el2) e2

plPlusInner :: Int -> Exp -> Exp
plPlusInner i e2 =
    case e2 of
      LamE sl el1 -> PlusE (LitE i) (LamE sl el1)
      AppE ea1 ea2 -> PlusE (LitE i) (AppE ea1 ea2)
      VarE s -> PlusE (LitE i) (VarE s)
      LitE i2 -> LitE (i + i2)
      PlusE ep1 ep2 -> PlusE (LitE i) (PlusE ep1 ep2)
      LetE s el1 el2 -> PlusE (LitE i) (LetE s el1 el2)

-- Example term

ex1 :: Exp
ex1 = (LetE (quote "x.1") (LitE 30)
                (LetE (quote "f.1") (LamE (quote "x.2") (PlusE (LitE 10) (VarE (quote "x.2"))))
                      (AppE (VarE (quote "f.1"))
                            (PlusE (VarE (quote "x.1")) (LitE 2)))))

buildLargeExp :: Int -> Exp
buildLargeExp n =
  if (n== 0 )
    then
       ex1
    else
      LetE (quote "xxxx") ex1 (buildLargeExp (n-1))



eval :: Val -> Int
eval v =
    case v of
      IntV i -> i
      LamV s e -> -1
      ErrorV -> -2


gibbon_main = (eval (interpExp (ptExp (constProp (buildLargeExp 100)))))

-- main :: IO ()
-- main = do
--   print (eval (interpExp (ptExp (constProp ex1))))
