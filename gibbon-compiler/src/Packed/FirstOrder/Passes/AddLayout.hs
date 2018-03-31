{-# LANGUAGE OverloadedStrings #-}

module Packed.FirstOrder.Passes.AddLayout where


import Data.Loc
import Data.List as L
import Data.Map as M
import Text.PrettyPrint.GenericPretty

import Packed.FirstOrder.Common
import Packed.FirstOrder.L1.Syntax

--------------------------------------------------------------------------------


type Size = Int
type SEnv = M.Map Var Size

type FunDef1 = FunDef Ty1 (L Exp1)

addLayout :: Prog -> SyM Prog
addLayout prg@Prog{ddefs,fundefs,mainExp} = do
  let iddefs = toIndrDDefs ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addLayoutFun iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just ex -> fmap Just (addLayoutExp iddefs M.empty ex)
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addLayoutFun :: DDefs Ty1 -> FunDef1 -> SyM FunDef1
addLayoutFun ddfs fd@FunDef{funBody} = do
  bod <- addLayoutExp ddfs M.empty funBody
  return $ fd{funBody = bod}

{- Note [Layout information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

addLayoutExp :: Out a => DDefs (UrTy a) -> SEnv -> L Exp1 -> SyM (L Exp1)
addLayoutExp ddfs senv (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numIndrsDataCon ddfs dcon of
        Just n  -> do
          let needSizeOf = take n args
          szs <- mapM (\arg -> do
                         v <- gensym "indr"
                         case inferSize senv arg of
                           Just sz -> return (v,[],IntTy, l$ LitE sz)
                           Nothing -> return (v,[],CursorTy, l$ PrimAppE PEndOf [arg]))
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
      let senv' = case inferSize senv rhs of
                    Nothing -> senv
                    Just sz -> M.insert v sz senv
      LetE <$> (v,loc,ty,) <$> go rhs <*> addLayoutExp ddfs senv' bod
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
    go = addLayoutExp ddfs senv

    docase :: (DataCon, [(Var,())], L Exp1) -> SyM (DataCon, [(Var,())], L Exp1)
    docase (dcon,vs,bod) = do
      case numIndrsDataCon ddfs dcon of
        Just n -> do
          szVars <- mapM (\_ -> (, ()) <$> gensym "sz") [1..n]
          (toIndrDataCon dcon, szVars ++ vs,) <$> go bod
        Nothing -> (dcon,vs,) <$> go bod

    -- | Minor optimization. Add literal int size fields where we can
    inferSize :: SEnv -> L Exp1 -> Maybe Size
    inferSize env (L _ ex') =
      case ex' of
        VarE v -> M.lookup v env
        LitE{}       -> sizeOf IntTy
        LitSymE{}    -> sizeOf SymTy
        PrimAppE f _ -> sizeOf (primRetTy f) -- or 8 ?
        LetE (v,_,_,rhs) bod -> case inferSize env rhs of
                                  Just sz -> inferSize (M.insert v sz env) bod
                                  Nothing -> inferSize env bod
        MkProdE ls -> sum <$> mapM (inferSize env) ls
        Ext _      -> Nothing
        DataConE _ _ args -> fmap (+1) $ sum <$> (mapM (inferSize env) args)
        _ -> Nothing
        -- AppE{} ->
        -- IfE a b c -> __
        -- ProjE i e -> __
        -- CaseE _ mp -> __
        -- TimeIt e ty b -> __


------------------------------------------------------------------------------------------

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
