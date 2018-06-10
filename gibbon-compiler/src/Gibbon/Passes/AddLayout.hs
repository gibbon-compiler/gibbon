{-# LANGUAGE OverloadedStrings #-}

module Gibbon.Passes.AddLayout
  (addLayout) where

import Data.Loc
import Data.List as L
import Data.Map as M
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

{- Note [Adding layout information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass runs after InferEffects.

Instead of using "dummy_traversals" as another program repair strategy in
InferLocations, it's easier to annotate the program first, and
then repair it later if required. `needsLayout` makes this decision.

Consider this example:

    main = add1 . buildtree

This example doesn't need to be repaired, and can be compiled in it's current form.
But on the other hand,

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

-- Operates on an L1 program, and updates it to have layout information

addLayout :: Prog1 -> PassM Prog1
addLayout prg@Prog{ddefs,fundefs,mainExp} = do
  let iddefs = toIndrDDefs ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addLayoutFun iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addLayoutExp iddefs ex
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addLayoutFun :: DDefs Ty1 -> L1.FunDef1 -> PassM L1.FunDef1
addLayoutFun ddfs fd@FunDef{funBody} = do
  bod <- addLayoutExp ddfs funBody
  return $ fd{funBody = bod}

addLayoutExp :: Out a => DDefs (UrTy a) -> L Exp1 -> PassM (L Exp1)
addLayoutExp ddfs (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numIndrsDataCon ddfs dcon of
        Just n  -> do
          let tys = lookupDataCon ddfs dcon
              packedOnly = L.map snd $
                           L.filter (\(ty,_) -> isPackedTy ty) (zip tys args)
              needSizeOf = L.take n packedOnly
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

    docase :: (DataCon, [(Var,())], L Exp1) -> PassM (DataCon, [(Var,())], L Exp1)
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
