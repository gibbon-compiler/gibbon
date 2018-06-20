module Gibbon.Passes.AddLayout
  (addLayout, numIndrsDataCon) where

import Data.Loc
import Data.List as L
import Data.Map as M
import Data.Maybe (fromJust)
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

{- Note [Adding layout information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot add layout information to an L2 program, as it would distort the locations
inferred by the previous analysis. Instead, (1) we use the old L1 program and
add layout information to that, (2) then run location inference again.

Adding layout information involves 3 steps:

(1) Convert DDefs to `WithLayout DDefs` (we don't have a separate type for those yet).

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

(2) Update all data constructors that now need to write additional indirection pointers
    (before all other arguments so that they're written immediately after the tag).

(3) Case expressions are modified to work with these updated data constructors.
    Pattern matches for these constructors now bind the additional indirections too.

-}

{- Note [Reusing indirections in case expressions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If a data constructor occurs inside a case expression, we might already have an
indirection for a variable that was bound in the pattern. In that case, we don't want
to request yet another one using PEndOf. Consider this example:

    (fn ...
      (case tr
        [(Node^ [(indr_y, _) (x, _), (y, _)]
           (DataConE __HOLE x (fn y)))]))

Here, we don't want to fill the HOLE with (PEndOf x). Instead, we should reuse indr_y.

-}

--------------------------------------------------------------------------------

type IndrEnv = M.Map Var Var

-- | Operates on an L1 program, and updates it to have layout information
addLayout :: Prog1 -> PassM Prog1
addLayout prg@Prog{ddefs,fundefs,mainExp} = do
  let iddefs = toIndrDDefs ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addLayoutFun iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addLayoutExp iddefs M.empty ex
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addLayoutFun :: DDefs Ty1 -> L1.FunDef1 -> PassM L1.FunDef1
addLayoutFun ddfs fd@FunDef{funBody} = do
  bod <- addLayoutExp ddfs M.empty funBody
  return $ fd{funBody = bod}

addLayoutExp :: DDefs Ty1 -> IndrEnv -> L Exp1 -> PassM (L Exp1)
addLayoutExp ddfs ienv (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numIndrsDataCon ddfs dcon of
        0 -> return ex
        n -> do
          let tys = lookupDataCon ddfs dcon
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              -- n elements after the first packed one require indirections.
              needIndrsFor = L.take n $ L.drop firstPacked args

          indrs <- mapM (\arg -> do
                           i <- gensym "indr"
                           -- See Note [Reusing indirections in case expressions]
                           let rhs = case unLoc arg of
                                       VarE x -> case M.lookup x ienv of
                                                   Just v -> VarE v
                                                   Nothing -> PrimAppE PEndOf [arg]
                                       _ -> PrimAppE PEndOf [arg]
                           return (i,[],CursorTy, l$ rhs))
                   needIndrsFor

          let indrArgs = L.map (\(v,_,_,_) -> l$ VarE v) indrs
          return $ unLoc $ mkLets indrs (l$ DataConE loc (toIndrDataCon dcon) (indrArgs ++ args))

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*> go bod
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
    go = addLayoutExp ddfs ienv

    docase :: (DataCon, [(Var,())], L Exp1) -> PassM (DataCon, [(Var,())], L Exp1)
    docase (dcon,vs,bod) = do
      case numIndrsDataCon ddfs dcon of
        0 -> (dcon,vs,) <$> go bod
        n -> do
          indrVars <- mapM (\_ -> gensym "indr") [1..n]
          let tys = lookupDataCon ddfs dcon
              -- See Note [Reusing indirections in case expressions]
              -- We update the environment to track indirections of the
              -- variables bound by this pattern.
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              haveIndrsFor = L.take n $ L.drop firstPacked $ L.map fst vs
              ienv' = M.union ienv (M.fromList $ zip haveIndrsFor indrVars)
          (toIndrDataCon dcon, (L.map (,()) indrVars) ++ vs,) <$> addLayoutExp ddfs ienv' bod

-- | Add "sized" constructors to the data definition
toIndrDDefs :: Out a => DDefs (UrTy a) -> Map Var (DDef (UrTy a))
toIndrDDefs ddfs = M.map go ddfs
  where
    -- go :: DDef a -> DDef b
    go dd@DDef{dataCons} =
      let dcons' = L.foldr (\(dcon,tys) acc ->
                              case numIndrsDataCon ddfs dcon of
                                0 -> (dcon,tys) : acc
                                n -> let tys'  = [(False,CursorTy) | _ <- [1..n]] ++ tys
                                         dcon' = toIndrDataCon dcon
                                     in [(dcon,tys), (dcon',tys')] ++ acc)
                   [] dataCons
      in dd {dataCons = dcons'}


-- | The number of indirections needed by a 'DataCon' for full random access
-- (which is equal the number of arguments occurring after the first packed type).
--
numIndrsDataCon :: Out a => DDefs (UrTy a) -> DataCon -> Int
numIndrsDataCon ddfs dcon =
  case L.findIndex isPackedTy tys of
    Nothing -> 0
    Just firstPacked -> (length tys) - firstPacked - 1
  where tys = lookupDataCon ddfs dcon
