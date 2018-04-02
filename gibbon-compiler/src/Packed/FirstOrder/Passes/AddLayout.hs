{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Packed.FirstOrder.Passes.AddLayout
  (addLayout, smartAddLayout) where

import Data.Loc
import Data.List as L
import Data.Map as M
import Data.Set as S
import Text.PrettyPrint.GenericPretty

import Packed.FirstOrder.Common
import Packed.FirstOrder.L1.Syntax
import qualified Packed.FirstOrder.L2.Syntax as L2

import Packed.FirstOrder.Passes.InferLocations (inferLocs)
import Packed.FirstOrder.Passes.InferEffects   (inferEffects)

import Debug.Trace

--------------------------------------------------------------------------------

{- Note [Adding layout information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass runs immediately after location inference & infereffects.

Instead of using "dummy_traversals" as another program repair strategy in
InferLocations, it's easier to annotate the program first, and
then repair it later if required. `needsLayout` makes this decision.

Consider this example:

    main = add1 . buildtree

This example doesn't need to be repaired, and can compile in it's current form. But
on the other hand, this program;

    main =  add1 . rightmost . buildtree

...won't, because `rightmost` doesn't traverse the left element of a node.
Instead of adding the traversal to `rightmost`, we take a step back, and add
layout information to the program. This basically allows O(1) random
access to any element of the node.

Note that we can't add layout information to an L2 program, as it would distort
the the location arithmetic. Instead, (1) we transform the program to L1 and
add layout information to that, (2) then run location inference on this updated
version.

Adding layout information involves 3 steps:

(1) Convert DDefs to `WithLayout DDefs` (we don't have a separate type for those yet).

(2) All data constructors that should have indirection pointers are updated.
    And the indirections are added at appropriate places (before all other arguments so that they're
    written immediately after the tag).

(3) Case expressions are modified to work with the modified data constructors.
    Pattern matches for these constructors now bind the additional size fields too.

For example,

    ddtree :: DDefs Ty1
    ddtree = fromListDD [DDef (toVar "Tree")
                          [ ("Leaf",[(False,IntTy)])
                          , ("Node",[ (False,PackedTy "Tree" ())
                                    , (False,PackedTy "Tree" ())])
                          ]]

becomes,

    ddtree :: DDefs Ty1
    ddtree = fromListDD [DDef (toVar "Tree")
                         [ ("Leaf"   ,[(False,IntTy)])
                         , ("Node",  [ (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         , ("Node^", [ (False, CursorTy) -- indirection pointer
                                     , (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         ]]
-}

--------------------------------------------------------------------------------

-- type LocEnv = M.Map Var (Int,LocVar)

-- | Add layout information to the program, but only if required
smartAddLayout :: L2.Prog -> SyM L2.Prog
smartAddLayout prg =
  if needsLayoutProg prg
  then do
    let l1 = L2.revertToL1 prg
    l1 <- addLayout l1
    l2 <- inferLocs l1
    l2 <- inferEffects l2
    return l2
  else return prg

-- Maybe we should use the Continuation monad here..
needsLayoutProg :: L2.Prog -> Bool
needsLayoutProg _ = True

-- needsLayoutExp :: L2.NewFuns -> LocEnv -> Int -> L L2.Exp2 -> Bool
-- needsLayoutExp fundefs lenv n (L _ ex) =
--   case ex of
--     CaseE scrt brs -> any id (L.map (docase n) brs)
--     Ext ext ->
--       case ext of
--         L2.LetRegionE r bod -> needsLayoutExp fundefs lenv (n+1) bod
--         L2.LetLocE loc rhs bod -> needsLayoutExp fundefs lenv (n+1) bod


--   where
--     docase n1 (dcon,vlocs,bod) =
--       let (vars,locs) = unzip vlocs
--           (n1',lenv') = L.foldr (\((var,loc), x) (_,acc) ->
--                                      (x, M.insert var (x,loc) acc))
--                         (n1,M.empty)
--                         (zip vlocs [n1..])
--       in trace (sdoc (n1',lenv')) (needsLayoutExp fundefs lenv' n1' bod)

--------------------------------------------------------------------------------

type FunDef1 = FunDef Ty1 (L Exp1)

addLayout :: Prog -> SyM Prog
addLayout prg@Prog{ddefs,fundefs,mainExp} = do
  let iddefs = toIndrDDefs ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addLayoutFun iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just ex -> fmap Just (addLayoutExp iddefs ex)
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addLayoutFun :: DDefs Ty1 -> FunDef1 -> SyM FunDef1
addLayoutFun ddfs fd@FunDef{funBody} = do
  bod <- addLayoutExp ddfs funBody
  return $ fd{funBody = bod}

addLayoutExp :: Out a => DDefs (UrTy a) -> L Exp1 -> SyM (L Exp1)
addLayoutExp ddfs (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numIndrsDataCon ddfs dcon of
        Just n  -> do
          let needSizeOf = take n args
          szs <- mapM (\arg -> do
                         v <- gensym "indr"
                         return (v,[],CursorTy, l$ PrimAppE PEndOf [arg]))
                 needSizeOf
          let szVars = L.map (\(v,_,_,_) -> v) szs
              szExps = L.map (l . VarE) szVars
          return $ unLoc $ mkLets szs (l$ DataConE loc (toIndrDataCon dcon) (szExps ++ args))
        Nothing -> return ex

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*> addLayoutExp ddfs bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE xs -> MkProdE <$> mapM go xs
    ProjE i e  -> ProjE i <$> go e
    CaseE scrt mp -> CaseE scrt <$> mapM docase mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    Ext _ -> return ex
    MapE{}  -> error "addLayoutExp: TODO MapE"
    FoldE{} -> error "addLayoutExp: TODO FoldE"

  where
    go = addLayoutExp ddfs

    docase :: (DataCon, [(Var,())], L Exp1) -> SyM (DataCon, [(Var,())], L Exp1)
    docase (dcon,vs,bod) = do
      case numIndrsDataCon ddfs dcon of
        Just n -> do
          szVars <- mapM (\_ -> (, ()) <$> gensym "sz") [1..n]
          (toIndrDataCon dcon, szVars ++ vs,) <$> go bod
        Nothing -> (dcon,vs,) <$> go bod

-- | Add "sized" constructors to the data definition
toIndrDDefs :: Out a => DDefs (UrTy a) -> Map Var (DDef (UrTy a))
toIndrDDefs ddfs = M.map go ddfs
  where
    -- go :: DDef a -> DDef a
    go dd@DDef{dataCons} =
      let dcons' = L.foldr (\(dcon,tys) acc ->
                              case numIndrsDataCon ddfs dcon of
                                Just n -> let tys'  = [(False,CursorTy) | _ <- [1..n]] ++ tys
                                              dcon' = toIndrDataCon dcon
                                          in [(dcon,tys), (dcon',tys')] ++ acc
                                Nothing -> (dcon,tys) : acc
                              )
                   [] dataCons
      in dd {dataCons = dcons'}
