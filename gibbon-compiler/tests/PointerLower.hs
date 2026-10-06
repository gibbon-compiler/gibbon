{-# LANGUAGE TemplateHaskell #-}

-- | Lowering in pointer mode (no --packed).
--
-- A boxed node is written once, by 'T.LetAllocT', as one struct holding the
-- tag and then the fields.  Every 'T.LetUnpackT' that reads a node back must
-- name that same struct: from the node itself, tag first.  Reading the fields
-- through a tag-less struct at node + 8 is a strict-aliasing violation, and
-- gcc -O3 -flto then deleted the constructor's stores (reduceNestedList
-- --pointer --c-arithmetic=unsafe read a NULL tail).
module PointerLower (pointerLowerTests) where

import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Language
import Gibbon.L3.Syntax
import Gibbon.L3.Typecheck (tcProg)
import qualified Gibbon.L4.Syntax as T
import Gibbon.Passes.Lower (lower)

listDDef :: DDef3
listDDef =
  DDef
    { tyName = "List"
    , tyArgs = []
    , dataCons =
        [ ("Nil", [])
        , ("Cons", [(False, IntTy W64), (False, PackedTy "List" ())])
        ]
    , memLayout = Linear
    }

-- | head0 xs = case xs of Nil -> 0; Cons a rst -> a
headFun :: FunDef3
headFun =
  FunDef "head0" ["xs"] ([PackedTy "List" ()], IntTy W64)
    (CaseE (VarE "xs")
       [ ("Nil", [], mkLitE64 0)
       , ("Cons", [("a", ()), ("rst", ())], VarE "a")
       ])
    (FunMeta NotRec NoInline False [] Nothing)

-- | one n = let nil = Nil in let c = Cons n nil in c
oneFun :: FunDef3
oneFun =
  FunDef "one" ["n"] ([IntTy W64], PackedTy "List" ())
    (LetE ("nil", [], PackedTy "List" (), DataConE () "Nil" [])
       (LetE ("c", [], PackedTy "List" (), DataConE () "Cons" [VarE "n", VarE "nil"])
          (VarE "c")))
    (FunMeta NotRec NoInline False [] Nothing)

lowered :: T.Prog
lowered = fst $ defaultRunPassM $ do
  prg <- tcProg True (Prog (M.fromList [("List", listDDef)])
                           (M.fromList [("head0", headFun), ("one", oneFun)])
                           Nothing)
  lower prg

loweredBody :: Var -> T.Tail
loweredBody f = case [ T.funBody fn | fn <- T.fundefs lowered, T.funName fn == f ] of
           [b] -> b
           _   -> error ("no lowered function " ++ fromVar f)

-- | (pointer, field types) of every unpack, and the field types of every
-- allocation, in a tail.
unpacks :: T.Tail -> [(Var, [T.Ty])]
unpacks tl = case tl of
  T.LetUnpackT{T.binds, T.ptr, T.bod} -> (ptr, map snd binds) : unpacks bod
  _ -> concatMap unpacks (subTails tl)

allocs :: T.Tail -> [[T.Ty]]
allocs tl = case tl of
  T.LetAllocT{T.vals, T.bod} -> map fst vals : allocs bod
  _ -> concatMap allocs (subTails tl)

subTails :: T.Tail -> [T.Tail]
subTails tl = case tl of
  T.LetCallT{T.bod}     -> [bod]
  T.LetPrimCallT{T.bod} -> [bod]
  T.LetTrivT{T.bod}     -> [bod]
  T.LetUnpackT{T.bod}   -> [bod]
  T.LetAllocT{T.bod}    -> [bod]
  T.IfT{T.con, T.els}   -> [con, els]
  T.Switch _ _ alts def ->
    let bs = case alts of
               T.TagAlts ls -> map snd ls
               T.IntAlts ls -> map snd ls
    in bs ++ maybe [] pure def
  _ -> []

case_sum_case_unpacks_the_scrutinee_with_its_tag :: Assertion
case_sum_case_unpacks_the_scrutinee_with_its_tag = do
  let us = unpacks (loweredBody "head0")
  assertBool "head0 should unpack its constructors" (not (null us))
  mapM_ (\(p, tys) -> do
           assertEqual "unpack pointer" (toVar "xs") p
           assertEqual "first unpacked field is the tag" (Just (T.IntTy W64))
                       (case tys of { (t:_) -> Just t; [] -> Nothing }))
        us

case_unpacks_read_the_struct_the_allocation_wrote :: Assertion
case_unpacks_read_the_struct_the_allocation_wrote = do
  let written = allocs (loweredBody "one")
      read    = map snd (unpacks (loweredBody "head0"))
  assertEqual "Nil and Cons are each allocated once" 2 (length written)
  mapM_ (\tys -> assertBool ("no allocation writes " ++ show tys) (tys `elem` written)) read

pointerLowerTests :: TestTree
pointerLowerTests = $(testGroupGenerator)
