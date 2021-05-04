{-# LANGUAGE NoImplicitPrelude #-}

module FoldConstants where

import Gibbon.Prelude

--------------------------------------------------------------------------------

data Exp = Lit Int
         | MkTrue
         | MkFalse
         | Plus Exp Exp
         | And Exp Exp
         | Or Exp Exp

trav_exp :: Exp -> ()
trav_exp exp =
  case exp of
    Lit i -> ()
    MkTrue -> ()
    MkFalse -> ()
    Plus a b -> let _ = trav_exp a
                    _ = trav_exp b
                in ()

print_exp :: Exp -> ()
print_exp exp =
  case exp of
    Lit i -> printint i
    MkTrue -> printsym (quote "True")
    MkFalse -> printsym (quote "False")
    Plus a b ->
      let _ = printsym (quote "(")
          _ = print_exp a
          _ = printsym (quote " + ")
          _ = print_exp b
          _ = printsym (quote ")")
      in ()

{-

foldConstants :: Exp -> Exp
foldConstants exp =
  case exp of
    Lit i -> Lit i
    MkTrue  -> MkTrue
    MkFalse -> MkFalse
    Plus a b ->
      case a of
        Lit i ->
          case b of
            Lit j -> Lit (i+j)
            Plus c d ->
              let a' = Lit i
                  c' = foldConstants c
                  d' = foldConstants d
              in Plus a' (Plus c' d')
        Plus c d ->
          let c' = foldConstants c
              d' = foldConstants d
              b' = foldConstants b
          in Plus (Plus c' d') b'

-}

islitConstant :: Float
{-# INLINE islitConstant #-}
islitConstant = 0.0 .-. 3.14

maybeLit :: Exp -> Float
maybeLit exp =
  case exp of
    Lit i -> intToFloat i
    Plus _ _ -> islitConstant

isLit :: Float -> Bool
isLit f = if ((f .-. islitConstant) .<. 0.01) then False else True

foldConstants2 :: Exp -> Exp
foldConstants2 exp =
  case exp of
    Lit i -> Lit i
    MkTrue  -> MkTrue
    MkFalse -> MkFalse
    Plus a b ->
      let maybe_alit = maybeLit a
      in if isLit maybe_alit
         then let _ = trav_exp a
                  maybe_blit = maybeLit b
              in if isLit maybe_blit
                 then let _ = trav_exp b
                      in Lit (floatToInt maybe_alit + floatToInt maybe_blit)
                 else let a' = (Lit (floatToInt maybe_alit))
                          b' = foldConstants2 b
                      in Plus a' b'
         else let a' = foldConstants2 a
                  b' = foldConstants2 b
              in Plus a' b'

foldConstants2_par :: Int -> Exp -> Exp
foldConstants2_par depth exp =
  if depth >= 8 then foldConstants2 exp else
  case exp of
    Lit i -> Lit i
    MkTrue  -> MkTrue
    MkFalse -> MkFalse
    Plus a b ->
      let maybe_alit = maybeLit a
      in if isLit maybe_alit
         then let _ = trav_exp a
                  maybe_blit = maybeLit b
              in if isLit maybe_blit
                 then let _ = trav_exp b
                      in Lit (floatToInt maybe_alit + floatToInt maybe_blit)
                 else let a' = (Lit (floatToInt maybe_alit))
                          b' = foldConstants2_par (depth+1) b
                      in Plus a' b'
         else
              let a' = spawn (foldConstants2_par (depth+1) a)
                  b' = foldConstants2_par (depth+1) b
                  _ = sync
              in Plus a' b'

buildExp :: Int -> Exp
buildExp n =
  if n == 0
  then Plus (Lit 0) (Lit 1)
  else Plus (buildExp (n-1)) (buildExp (n-1))

sumExp :: Exp -> Int
sumExp exp =
  case exp of
    Lit i -> i
    Plus a b ->
      sumExp a + sumExp b

gibbon_main =
  let -- exp = Plus (Plus (Lit 1) (Lit 2)) (Plus (Lit 1) (Lit 2))
      -- exp1 = foldConstants2_par exp
      -- _ = print_exp exp1
      -- _ = print_newline()
      exp = buildExp sizeParam
      -- exp2 = iterate (foldConstants2_par 0 exp)
      -- m = sumExp exp2
      exp1 = iterate (foldConstants2 exp)
      n = sumExp exp1
  in n


{-

type Ty = Sym

intTy :: Sym
{-# INLINE intTy #-}
intTy = quote "Int"

boolTy :: Sym
{-# INLINE boolTy #-}
boolTy = quote "Bool"

errorTy :: Sym
{-# INLINE errorTy #-}
errorTy = quote "Error"

--------------------------------------------------------------------------------

typecheck :: Exp -> (Ty, Exp)
typecheck exp =
  case exp of
    Lit i -> (intTy, Lit i)
    MkTrue   -> (boolTy, MkTrue)
    MkFalse  -> (boolTy, MkFalse)
    Plus a b ->
      let (ty1, a') = typecheck a
          (ty2, b') = typecheck b
          exp' = Plus a' b'
      in if eqsym ty1 intTy && eqsym ty2 intTy
         then (intTy, exp')
         else (errorTy, exp')

typecheck_par :: Exp -> (Ty, Exp)
typecheck_par exp =
  case exp of
    Lit i -> (intTy, Lit i)
    MkTrue -> (boolTy, MkTrue)
    MkFalse -> (boolTy, MkFalse)
    Plus a b ->
      let (ty1, a') = spawn (typecheck_par a)
          (ty2, b') = typecheck_par b
          _ = sync
          exp' = Plus a' b'
      in if eqsym ty1 intTy && eqsym ty2 intTy
         then (intTy, exp')
         else (errorTy, exp')

-}
