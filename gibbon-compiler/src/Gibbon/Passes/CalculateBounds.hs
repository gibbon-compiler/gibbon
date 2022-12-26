{-# LANGUAGE FlexibleInstances #-}
module Gibbon.Passes.CalculateBounds ( inferRegSize ) where

import           Gibbon.Common
import qualified Data.Map                      as M
import           Gibbon.L2.Syntax
-- import           Debug.Trace
import qualified Data.List as L

type LocationRegionMapping = M.Map LocVar Var
type LocationOffsetMapping = M.Map LocVar RegionSize
type VarSizeMapping = M.Map Var RegionSize
type VarLocMapping = M.Map Var LocVar
type RegionSizeMapping = M.Map Var RegionSize
type RegionTypeMapping = M.Map Var RegionType

inferRegSize :: Prog2 -> PassM Prog2
inferRegSize = calculateBounds

calculateBounds :: Prog2 -> PassM Prog2
calculateBounds Prog { ddefs, fundefs, mainExp } = do
  let env2 = Env2 M.empty (initFunEnv fundefs)
  fundefs' <- mapM (calculateBoundsFun ddefs env2 M.empty) fundefs
  mainExp' <- case mainExp of
    Nothing       -> return Nothing
    Just (mn, ty) -> Just . (, ty) . fst3 <$> calculateBoundsExp ddefs env2 M.empty M.empty M.empty M.empty M.empty M.empty mn
  return $ Prog ddefs fundefs' mainExp'


calculateBoundsFun :: DDefs Ty2 -> Env2 Ty2 -> VarSizeMapping -> FunDef2 -> PassM FunDef2
calculateBoundsFun ddefs env2 varSzEnv f@FunDef { funName, funBody, funTy, funArgs } = do
  if "_" `L.isPrefixOf` fromVar funName
    then return f
    else do
      let locRegEnv = M.fromList $ map (\lv -> (lrmLoc lv, regionToVar $ lrmReg lv)) (locVars funTy)
      let locTyEnv  = M.map (const $ BoundedSize 0) locRegEnv
      let argTys    = M.fromList $ zip funArgs (arrIns funTy)
      let env2'     = env2 { vEnv = argTys }
      funBody' <- fst3 <$> calculateBoundsExp ddefs env2' varSzEnv M.empty locRegEnv locTyEnv M.empty M.empty funBody
      return $ f { funBody = funBody' }

{-
  * We recurse using three mappings (variable => size, location => region and region => size)
  * 1. the variable => size mapping is inferred using type of the variable
  * 2. the location => region mapping is inferred using threading location initializations
  *     using LocVars
  * 3. the region => size mapping is calculated by adding up the incremental offsets from
  *     previous location in the same reigon and then adding the size of the last location/variable
  *     size in the region
  *
  * While recursing we return the
  * 1. the updated expression (i.e. possibly attaching the size of the regions in the expression)
  * 2. the region to size mapping in the expression (which can be used to find maximum size
  *     from all the branches)
  * 3. the region to type mapping in the expression -> based on indirections
  *
  * NOTE: since input and output regions are not created inside the function,
  * we will not update the region size inside that function .
-}
calculateBoundsExp
  :: DDefs Ty2 -- ^ Data Definitions
  -> Env2 Ty2 -- ^ Type Environment (Variables + Functions)
  -> VarSizeMapping -- ^ var => size
  -> VarLocMapping -- ^ var => location
  -> LocationRegionMapping -- ^ location => region
  -> LocationOffsetMapping -- ^ location => offset
  -> RegionSizeMapping -- ^ region => size
  -> RegionTypeMapping -- ^ region => type
  -> Exp2 -- ^ expression
  -> PassM (Exp2, RegionSizeMapping, RegionTypeMapping)
calculateBoundsExp ddefs env2 varSzEnv varLocEnv locRegEnv locOffEnv regSzEnv regTyEnv ex = case ex of
  Ext (BoundsCheck{}) -> return (ex, regSzEnv, regTyEnv)
  Ext (IndirectionE _tycon _dcon (fromLoc, _fromvar) (toLoc, _tovar) _exp) -> do
    let fromReg = locRegEnv # fromLoc
    let fromOff = locOffEnv # fromLoc
    let toOff   = locOffEnv # toLoc
    let regTy = M.findWithDefault IndirectionFree fromReg regTyEnv <> if toOff >= fromOff then RightwardLocalIndirections else LocalIndirections
    let regSz   = fromOff <> BoundedSize 9
    return (ex, M.insert fromReg regSz regSzEnv, M.insert fromReg regTy regTyEnv)
  VarE _ -> return (ex, regSzEnv, regTyEnv)
  _ ->
    let ty   = gRecoverType ddefs env2 ex
        go   = calculateBoundsExp ddefs env2 varSzEnv varLocEnv locRegEnv locOffEnv regSzEnv regTyEnv
        err  = error "Should have been covered by sizeOfTy"
        pass = return (ex, regSzEnv, regTyEnv)
    in  case sizeOfTy ty of
          Just _ -> return (ex, regSzEnv, regTyEnv)
          _      -> case ex of
            LitE    _           -> err
            CharE   _           -> err
            FloatE  _           -> err
            LitSymE _           -> err
            ProjE{}             -> pass
            TimeIt{}            -> pass
            WithArenaE{}        -> pass
            SpawnE{}            -> pass
            SyncE{}             -> pass
            MapE{}              -> pass
            FoldE{}             -> pass
            AppE _v _locs _args -> do
              -- TODO traversals
              return (ex, regSzEnv, regTyEnv)
            PrimAppE{}             -> return (ex, regSzEnv, regTyEnv)
            DataConE loc dcon args -> do
              (_, res, rts) <- unzip3 <$> mapM go args
              return (DataConE loc dcon args, mconcat res, mconcat rts)
            IfE cond bod1 bod2 -> do
              (bod1', regSzEnv1, regTyEnv1) <- go bod1
              (bod2', regSzEnv2, regTyEnv2) <- go bod2
              return (IfE cond bod1' bod2', M.unionWith max regSzEnv1 regSzEnv2, regTyEnv1 <> regTyEnv2)
            MkProdE ls -> do
              (ls', regSzEnvs, regTyEnvs) <- unzip3 <$> mapM go ls
              return (MkProdE ls', M.unionsWith max regSzEnvs, M.unions regTyEnvs)
            LetE (v, locs, ty0, bind) bod -> do
              (bind', regSzEnv', regTyEnv') <- go bind
              let venv' = M.insert v ty0 (vEnv env2)
              let vle = case ty0 of
                    PackedTy _tag loc -> M.insert v loc varLocEnv
                    _                 -> varLocEnv
              (bod', regSzEnv'', regTyEnv'') <- calculateBoundsExp ddefs env2 { vEnv = venv' } varSzEnv vle locRegEnv locOffEnv regSzEnv regTyEnv bod
              let regSzEnv3 = M.unionWith max regSzEnv' regSzEnv''
              let regSzEnv4 = case ty0 of
                    -- TODO sizeofTy ty0 is incalculable? -> assume as 0 to give preference to analysis in other locations
                    PackedTy _tag loc ->
                      -- Make the chunk at least 32 bytes.
                      let sz = case (locOffEnv # loc <> (maybe (BoundedSize 0) BoundedSize . sizeOfTy) ty0) of
                                 BoundedSize i -> BoundedSize (max i 32)
                                 Undefined -> Undefined
                      in M.insertWith max (locRegEnv # loc) sz regSzEnv3
                    _ -> regSzEnv3
              return (LetE (v, locs, ty0, bind') bod', regSzEnv4, M.union regTyEnv' regTyEnv'')
            CaseE ex2 cases -> do
              (cases', res, rts) <-
                unzip3
                  <$> mapM
                        (\(dcon :: DataCon, vlocs :: [(Var, LocVar)], bod :: Exp2) -> do
                          -- TODO use for traversal somewhere down the line?
                          -- let offsets =
                          --       M.fromList
                          --         . tail -- remove tag
                          --         . scanl1 (\(_, s1) (v2, s2) -> (v2, s1 <> s2)) -- accumulate offsets
                          --         . ((undefined, BoundedSize 1) :)  -- add size for tag
                          --         . zip (map snd vlocs) -- take locations
                          --         . map (maybe Undefined BoundedSize . sizeOfTy) -- map to our region size type
                          --         $ lookupDataCon ddefs dcon -- find ddef)
                          let venv' = M.union (M.fromList $ zip (map fst vlocs) (lookupDataCon ddefs dcon)) (vEnv env2)
                              varLocEnv' = M.fromList vlocs `M.union` varLocEnv
                              (_vars,locs) = unzip vlocs
                              locOffEnv' = (M.fromList (zip locs (repeat Undefined))) `M.union` locOffEnv
                          (bod', re, rt) <- calculateBoundsExp ddefs (env2 { vEnv = venv'}) varSzEnv varLocEnv' locRegEnv locOffEnv' regSzEnv regTyEnv bod
                          return ((dcon, vlocs, bod'), re, rt)
                        )
                        cases
              return (CaseE ex2 cases', M.unionsWith max res, M.unions rts)
            Ext ext -> case ext of
              LetRegionE reg _ _ bod -> do
                (bod', re, rt) <- go bod
                let regVar = regionToVar reg
                let regSz  = re # regVar
                let regTy = Just $ M.findWithDefault IndirectionFree regVar rt
                dbgTrace 4 (">> Region: " ++ show reg ++ " -> " ++ show regSz ++ " : " ++ show regTy) $
                  return (Ext $ LetRegionE reg regSz regTy bod', re, rt)
              LetParRegionE reg _ _ bod -> do
                (bod', re, rt) <- go bod
                let regVar = regionToVar reg
                let regSz  = re # regVar
                let regTy = Just $ M.findWithDefault IndirectionFree regVar rt
                dbgTrace 4 (">> Region: " ++ show reg ++ " -> " ++ show regSz ++ " : " ++ show regTy) $
                  (return (Ext (LetParRegionE reg regSz regTy bod'), re, rt))
              LetLocE loc locExp ex1 -> do
                -- * NOTE: jumps are only necessary for route ends, skipping them.
                if "jump_" `L.isPrefixOf` fromVar loc
                  then do
                    (ex1', re', rt') <- go ex1
                    return (Ext $ LetLocE loc locExp ex1', re', rt')
                  else do
                    let (re, off) = case locExp of
                          (StartOfRegionLE r          ) -> (regionToVar r, BoundedSize 0)
                          (AfterConstantLE n l  ) -> (locRegEnv # l, locOffEnv # l <> BoundedSize n)
                          (AfterVariableLE v l _) -> (locRegEnv # l, locOffEnv # (varLocEnv # v) <> varSzEnv # v)
                          (InRegionLE r         ) -> (regionToVar r, Undefined)
                          (FromEndLE  l         ) -> (locRegEnv # l, Undefined)
                          FreeLE                  -> undefined
                    let lre = M.insert loc re locRegEnv
                    let loe = M.insert loc off locOffEnv
                    (ex1', re', rt') <- calculateBoundsExp ddefs env2 varSzEnv varLocEnv lre loe regSzEnv regTyEnv ex1
                    return (Ext $ LetLocE loc locExp ex1', re', rt')
              RetE _locs v -> do
                (_, re, rt) <- go (VarE v)
                return (ex, re, rt)
              FromEndE{}         -> pass
              AddFixed{}         -> pass
              GetCilkWorkerNum{} -> pass
              LetAvail vs e      -> do
                (e', re', rt') <- go e
                return (Ext $ LetAvail vs e', re', rt')
              StartOfPkdCursor{}    -> error $ "todo: " ++ sdoc ex
              TagCursor{}           -> error $ "todo: " ++ sdoc ex
              AllocateTagHere{}     -> error $ "todo: " ++ sdoc ex
              AllocateScalarsHere{} -> error $ "todo: " ++ sdoc ex
              SSPush{}              -> error $ "todo: " ++ sdoc ex
              SSPop{}               -> error $ "todo: " ++ sdoc ex
