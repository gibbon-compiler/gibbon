{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
-- {-# OPTIONS_GHC -Wall #-}


--- Rough translation of L1 language from Redex model to Haskell.
---
--- Soon this can either be merged with the existing.L1.Syntax module,
--- discarded in favor of direcly modifying.L1.Syntax, or expanded
--- to replace.L1.Syntax.
---
--- Design goals:
---  * Mirror the design of the language in the redex model reasonably closely.
---  * Share some structure with existing AST types (ie. use Common module).
---  * Avoid fancy parameterized types for now.
---
--- Overall picture:
--- A program consists of a series of data type definitions (DDefs, unchanged),
--- a series of function definitions, and an optional expression. Functions
--- now separately take both a normal argument list and a list of in/out
--- locations. Expressions have different let binding forms for locations,
--- packed data, non-packed data, and regions.
---
--- Big differences from model (so far): arbitrary tuple sizes, and arbitrary
--- data types (not just leaf/node).
---
--- Since this language requires that we thread through location information
--- and do computation in the right order, it's not suitable as a direct
--- target from Racket (yet). This can be worked out as we integrate it
--- into the full compiler. Possibilities:
---  * AST will be translated to this IR once we infer location info.
---  * This language is extended with indirection and all source programs
---    start out using only indirection, to be changed by later optimization.

module Gibbon.LocExp where

import Gibbon.Common
import Data.Map as M
import Data.Set as S
import Data.List as L
import GHC.Generics
import Text.PrettyPrint.GenericPretty
import Control.DeepSeq (NFData)

type Loc = LocVar
data Reg = Var


data LocProgram = LocProgram (DDefs Ptype) (Map Var Fdef) (Maybe Exp)
                  deriving (Read,Show,Eq,Ord, Generic, NFData)

data Fdef = Fdef Var Ftype [Rp] [Var] Exp
            deriving (Read,Show,Eq,Ord, Generic, NFData)

data Rp = LocIn Loc Reg
        | LocOut Loc Reg
          deriving (Read,Show,Eq,Ord, Generic, NFData)

data Ftype = PrimType Ptype
           | FunType [Rp] Ptype Ptype
             deriving (Read,Show,Eq,Ord, Generic, NFData)

data Ptype = ProdType [Ptype]
           | IntType
           | BoolType
           | SymType
           | DictType Ptype
           | PackedType Var Loc
             deriving (Read,Show,Eq,Ord, Generic, NFData)

data Exp = VarE Var
         | LitE Int
         | LitSymE Var
         | AppE Var [Rp] [Exp]
         | PrimAppE Prim [Exp]
         | LetPackedE Var Ptype Exp Exp
         | LetRegionE Reg Exp
         | LetLocE Var LocExp Exp
         | LetE Var Ptype Exp Exp
         | MkProdE [Exp]
         | DataConE DataCon Loc [Exp]
         | ProjE Int Exp
         | IfE Exp Exp Exp
         | CaseE Exp (Map DataCon ([(Var,Loc,Ptype)],Exp))
           deriving (Read,Show,Eq,Ord, Generic, NFData)

data LocExp = StartL Reg
            | PlusCL Int Loc
            | PlusSizeOfL Var Loc
              deriving (Read,Show,Eq,Ord, Generic, NFData)

--- TODO: share Prim (put in Common maybe?)
data Prim = AddP | SubP | MulP -- ^ May need more numeric primitives...
          | EqSymP          -- ^ Equality on Sym
          | EqIntP       -- ^ Equality on Int
          | DictInsertP Ptype  -- ^ takes dict, k,v; annotated with element type
          | DictLookupP Ptype  -- ^ takes dict,k errors if absent; annotated with element type
          | DictEmptyP Ptype   -- ^ annotated with element type to avoid ambiguity
          | DictHasKeyP Ptype  -- ^ takes dict,k; returns a Bool, annotated with element type
          | ErrorP String Ptype
              -- ^ crash and issue a static error message.
              --   To avoid needing inference, this is labeled with a return type.
          | MkTrue -- ^ Zero argument constructor.
          | MkFalse -- ^ Zero argument constructor.
            deriving (Read,Show,Eq,Ord, Generic, NFData)

voidType :: Ptype
voidType = ProdType []


hasPacked :: Ptype -> Bool
hasPacked (ProdType ls) = any hasPacked ls
hasPacked (PackedType _ _) = True
hasPacked IntType = False
hasPacked BoolType = False
hasPacked SymType = False
hasPacked (DictType ty) = hasPacked ty


freeVars :: Exp -> Set Var
freeVars (VarE v) = S.singleton v
freeVars (LitE _) = S.empty
freeVars (LitSymE _) = S.empty
freeVars (AppE _v _ ls) = S.unions (L.map freeVars ls)
freeVars (PrimAppE _ ls) = S.unions (L.map freeVars ls)
freeVars (LetPackedE v _ e1 e2) = S.union (freeVars e1) (S.delete v (freeVars e2))
freeVars (LetRegionE _ e) = freeVars e
freeVars (LetLocE v1 (PlusSizeOfL v2 _) e) = S.union (S.singleton v2) (S.delete v1 (freeVars e))
freeVars (LetLocE v _ e) = S.delete v (freeVars e)
freeVars (LetE v _ e1 e2) = S.union (freeVars e1) (S.delete v (freeVars e2))
freeVars (MkProdE ls) = S.unions (L.map freeVars ls)
freeVars (DataConE _ _ ls) = S.unions (L.map freeVars ls)
freeVars (ProjE _ e) = freeVars e
freeVars (IfE e1 e2 e3) = S.unions [freeVars e1, freeVars e2, freeVars e3]
freeVars (CaseE e mp) = S.union (freeVars e) $ S.unions $ L.map (freeVars . snd . snd) $ M.toList mp

data Constr = StartOfC Loc Reg
            | After1C Int Loc Loc
            | AfterXC Var Loc Loc
            | InC Loc Reg
              deriving (Read,Show,Eq,Ord, Generic, NFData)

data LocState = InLS Loc
              | OutLS Loc
              | AfterLS Loc
              | StartS Reg
                deriving (Read,Show,Eq,Ord, Generic, NFData)

--- TODO: finish typechecker
--- does it need to be monadic, or can it be pure?
typeofE :: DDefs Ptype -> (Map Var Ftype) -> (Set Constr) -> (Set Reg) -> (Set LocState) -> Exp ->
           (Ftype,Set LocState)
typeofE dd g c r ls exp =
    case exp of
      VarE v -> case M.lookup v g of
                  Just t -> (t, ls)
                  Nothing -> error ("Failed to lookup variable " ++ (show v)
                                   ++ " in gamma: " ++ (show g))

      LitE _ -> (PrimType IntType, ls)

      LitSymE _ -> (PrimType SymType, ls)

      LetPackedE v pt e1 e2 -> let (t1, ls1) = typeofE dd g c r ls e1
                               in if (t1 == (PrimType pt)) then typeofE dd (M.insert v (PrimType pt) g) c r ls1 e2
                                  else error ("Type of let bound expression was " ++ (show t1)
                                             ++ " but expected " ++ (show pt) ++ " for exp: "
                                             ++ (show e1))

      LetRegionE r' exp -> typeofE dd g c (S.insert r' r) ls exp

      LetE v pt e1 e2 ->
          if hasPacked pt then error ("Expected unpacked type, found " ++ (show pt))
          else let (t1, ls1) = typeofE dd g c r ls e1
               in if (t1 == (PrimType pt)) then typeofE dd (M.insert v (PrimType pt) g) c r ls1 e2
                  else error ("Type of let bound expression was " ++ (show t1)
                             ++ " but expected " ++ (show pt) ++ " for exp: "
                             ++ (show e1))

      AppE v rps exps -> case M.lookup v g of
                           Just t -> undefined
                           Nothing -> error ("Failed to lookup variable " ++ (show v)
                                            ++ " in gamma: " ++ (show g))
      LetLocE v le exp -> case le of
                            StartL r' -> let c' = S.union c $ S.fromList [StartOfC v r', InC v r']
                                         in typeofE dd g c' r ls exp
                            PlusCL i l -> let r' = findRegion r c l
                                              c' = S.union c $ S.fromList [InC v r', After1C i l v]
                                              ls' = S.union ls $ S.fromList [OutLS v, AfterLS l]
                                          in noAfter l ls $ typeofE dd g c' r ls' exp
                            PlusSizeOfL v' l' -> case M.lookup v g of
                                                   Just (PrimType (PackedType v'' l'')) ->
                                                       if l' == l'' -- should be equal!
                                                       then undefined
                                                       else let r' = findRegion r c l'
                                                                c' = S.union c $ S.fromList [AfterXC v' l' v, InC v r']
                                                                ls' = S.union ls $ S.fromList [AfterLS l', OutLS v]
                                                            in noAfter l' ls $ typeofE dd g c' r ls' exp
                                                   _ -> undefined
      MkProdE exps -> f ls exps
          where f ls (e:es) = let (PrimType t,ls') = typeofE dd g c r ls e
                                  (PrimType (ProdType ts),ls'') = f ls' es
                              in (PrimType $ ProdType $ S.toList $ S.union (S.singleton t) (S.fromList ts), ls'')
                f ls [] = (PrimType $ voidType, ls)

      ProjE i exp -> let (PrimType (ProdType ts),ls') = typeofE dd g c r ls exp
                     in (PrimType $ ts !! i, ls')

      IfE e1 e2 e3 -> let (t1,ls') = typeofE dd g c r ls e1
                          (t2,ls'') = typeofE dd g c r ls' e2
                          (t3,ls''') = typeofE dd g c r ls'' e3
                      in if t1 == PrimType (BoolType) && t2 == t3 then (t3,ls''') else undefined

      DataConE v l exps -> undefined

      PrimAppE p exps -> undefined

      CaseE exp mp -> undefined

findRegion :: (Set Reg) -> (Set Constr) -> Loc -> Reg
findRegion r c l = case S.foldr f Nothing c of
                     Nothing -> undefined
                     Just reg -> if S.member reg r then reg
                                 else error ("Region " ++ (show reg) ++ " not in environment.")
    where f (InC loc reg) a = if l == loc then Just reg else a
          f _c a = a

noAfter :: Loc -> (Set LocState) -> a -> a
noAfter = undefined

-- Pure interpreter
interpProg :: LocProgram -> Exp
interpProg = fst . runSyM 0 . interpProg'

interpProg' :: LocProgram -> SyM Exp
interpProg' (LocProgram _ _ Nothing) = error "Can't interpret program with no main expression"
interpProg' (LocProgram _dd fenv (Just e)) = interpE fenv M.empty e

interpE :: (Map Var Fdef) -> (Map Var Exp) -> Exp -> SyM Exp
interpE fenv env exp =
    case exp of
      VarE v -> case M.lookup v env of
                  Just e -> return e
                  Nothing -> error ("Variable " ++ (show v) ++ " not found in env: " ++ (show env))

      LitE i -> return $ LitE i

      LitSymE s -> return $ LitSymE s

      AppE v _ exps -> case M.lookup v fenv of
                         Just (Fdef _ _ _ vs e) ->
                             do exps' <- mapM (interpE fenv env) exps
                                let env' = M.union (M.fromList (zip vs exps')) env
                                interpE fenv env' e
                         Nothing -> error ("Function with name " ++ (show v) ++ " not found in fenv: " ++ (show fenv))

      LetPackedE v _ e1 e2 -> do e1' <- interpE fenv env e1
                                 let env' = M.insert v e1' env
                                 interpE fenv env' e2

      LetRegionE _ exp _ -> interpE fenv env exp

      LetLocE _ _ exp -> interpE fenv env exp

      LetE v _ e1 e2 -> do e1' <- interpE fenv env e1
                           let env' = M.insert v e1' env
                           interpE fenv env' e2

      MkProdE exps -> do exps' <- mapM (interpE fenv env) exps
                         return $ MkProdE exps'

      DataConE v l exps -> do exps' <- mapM (interpE fenv env) exps
                               return $ DataConE v l exps'

      ProjE i exp -> do exp' <- interpE fenv env exp
                        case exp' of
                          MkProdE exps -> return $ exps !! i
                          _ -> undefined

      IfE e1 e2 e3 -> do e1' <- interpE fenv env e1
                         case e1' of
                           PrimAppE MkTrue [] -> interpE fenv env e2
                           PrimAppE MkFalse [] -> interpE fenv env e3
                           _ -> undefined

      CaseE exp mp ->
          do exp' <- interpE fenv env exp
             case exp' of
               DataConE v _ exps -> case M.lookup v mp of
                                       Just (bnds,e) -> let vs = L.map (\(v,_,_) -> v) bnds
                                                            env' = M.union (M.fromList (zip vs exps)) env
                                                        in interpE fenv env' e
                                       Nothing -> undefined
               _ -> error ("Expected case of packed data, got " ++ (show exp'))

      PrimAppE p exps ->
          case p of
            AddP -> do let [e1,e2] = exps
                       (LitE i1) <- interpE fenv env e1
                       (LitE i2) <- interpE fenv env e2
                       return $ LitE (i1 + i2)
            SubP -> do let [e1,e2] = exps
                       (LitE i1) <- interpE fenv env e1
                       (LitE i2) <- interpE fenv env e2
                       return $ LitE (i1 - i2)
            MulP -> do let [e1,e2] = exps
                       (LitE i1) <- interpE fenv env e1
                       (LitE i2) <- interpE fenv env e2
                       return $ LitE (i1 * i2)
            EqIntP -> do let [e1,e2] = exps
                         (LitE i1) <- interpE fenv env e1
                         (LitE i2) <- interpE fenv env e2
                         return $ if (i1 == i2) then PrimAppE MkTrue [] else PrimAppE MkFalse []
            EqSymP -> do let [e1,e2] = exps
                         (LitSymE i1) <- interpE fenv env e1
                         (LitSymE i2) <- interpE fenv env e2
                         return $ if (i1 == i2) then PrimAppE MkTrue [] else PrimAppE MkFalse []
            MkTrue -> return $ PrimAppE MkTrue []
            MkFalse -> return $ PrimAppE MkFalse []




--- examples

testProg :: LocProgram
testProg = LocProgram (fromListDD [DDef "Tree" True
                              [ ("Leaf",[IntType])
                              , ("Node",[PackedType "Tree" "l1", PackedType "Tree" "l2"])]])
           M.empty
           (Just (withTree (caseOnTree "tr")))

add1Prog :: LocProgram
add1Prog = LocProgram (fromListDD [DDef "Tree" True
                              [ ("Leaf",[IntType])
                              , ("Node",[PackedType "Tree" "l1", PackedType "Tree" "l2"])]])
           (M.fromList [("add1",add1Fun),("sum",sumFun)])
           (Just add1Test)

add1Fun :: Fdef
add1Fun = Fdef "add1"
          add1Type
          [(LocIn "l1" "r1"),
           (LocOut "l2" "r2")]
          ["tr"]
          add1Body

sumFun :: Fdef
sumFun = Fdef "sum"
         sumType
         [(LocIn "l1" "r1")]
         [("tr")]
         sumBody

add1Type :: Ftype
add1Type = FunType
           [(LocIn "l1" "r1"),
            (LocOut "l2" "r2")]
           (PackedType "Tree" "l1") (PackedType "Tree" "l2")

sumType :: Ftype
sumType = FunType
          [(LocIn "l1" "r1")]
          (PackedType "Tree" "l1") IntType

add1Body :: Exp
add1Body = CaseE (VarE "tr") $
           M.fromList [("Leaf", ([("n","ln",IntType)],
                                 DataConE "Leaf" "l2" [PrimAppE AddP [(VarE "n"),(LitE 1)]])),
                       ("Node", ([("x","lx",PackedType "Tree" "lx"),("y","ly",PackedType "Tree" "ly")],
                                 nodeCase))]

nodeCase :: Exp
nodeCase = LetLocE "l3" (PlusCL 1 "l2") $
           LetPackedE "x2" (PackedType "Tree" "l3")
                      (AppE "add1" [LocIn "lx" "r1",LocOut "l3" "r2"] [(VarE "x")]) $
           LetLocE "l4" (PlusSizeOfL "x2" "l3") $
           LetPackedE "y2" (PackedType "Tree" "l4")
                      (AppE "add1" [LocIn "ly" "r1",LocOut "l4" "r2"] [(VarE "y")]) $
           DataConE "Node" "l2" [VarE "x2", VarE "y2"]

sumBody :: Exp
sumBody = CaseE (VarE "tr") $
           M.fromList [("Leaf", ([("n","ln",IntType)],
                                 (VarE "n"))),
                       ("Node", ([("x","lx",PackedType "Tree" "lx"),("y","ly",PackedType "Tree" "ly")],
                                 LetE "n1" IntType (AppE "sum" [LocIn "lx" "r1"] [(VarE "x")]) $
                                 LetE "n2" IntType (AppE "sum" [LocIn "ly" "r1"] [(VarE "y")]) $
                                 PrimAppE AddP [(VarE "n1"),(VarE "n2")]))]

add1Test :: Exp
add1Test = withTree $
           LetLocE "o" (StartL "r2") $
           LetPackedE "tradd" (PackedType "Tree" "o")
                      (AppE "add1" [LocIn "l" "r1", LocOut "o" "r2"] [(VarE "tr")]) $
           AppE "sum" [LocIn "o" "r2"] [(VarE "tradd")]

withTree :: Exp -> Exp
withTree e = LetRegionE "r1" $
             LetRegionE "r2" $
             LetLocE "l" (StartL "r1") $
             LetLocE "l1" (PlusCL 1 "l") $
             LetPackedE "tr1" (PackedType "Tree" "l1") (DataConE "Leaf" "l1" [(LitE 1)]) $
             LetLocE "l2" (PlusSizeOfL "tr1" "l1") $
             LetPackedE "tr2" (PackedType "Tree" "l2") (DataConE "Leaf" "l2" [(LitE 2)]) $
             LetPackedE "tr" (PackedType "Tree" "l") (DataConE "Node" "l" [(VarE "tr1"),(VarE "tr2")]) $
             e

caseOnTree :: Var -> Exp
caseOnTree v = CaseE (VarE v) $
               M.fromList [("Leaf", ([("n","ln",IntType)],
                                     (LitE 1))),
                           ("Node", ([("x","lx",PackedType "Tree" "lx"),("y","ly",PackedType "Tree" "ly")],
                                     (LitE 2)))]
