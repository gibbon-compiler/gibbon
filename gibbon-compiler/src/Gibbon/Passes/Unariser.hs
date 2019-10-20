module Gibbon.Passes.Unariser
  (unariser, unariserExp) where

import Data.Loc
import qualified Data.Map as M
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L3.Syntax


-- | This pass gets ready for Lower by converting most uses of
-- projection and tuple-construction into finer-grained bindings.
--
-- OUTPUT INVARIANTS:
--
-- (1) only flat tuples as function arguments (no nesting), all
-- arguments immediately present, e.g. `AppE "f" (MkProd [x,y,z])`
--  rather than `AppE "f" (MkProdE [x,MkProdE[y,z]])`
--
-- (2) The only MkProdE allowed outside of function operands is within
-- return/tail position (of a function or If branch).
--
-- (3) Primitives are allowed to return tuples, but are let-bound
-- (these will turn into LetPrimCall).  The references to these tuples
-- are all of the form `ProjE i (VarE v)` and they are then
-- transformed to varrefs in lower.
--

unariser :: Prog3 -> PassM Prog3
unariser Prog{ddefs,fundefs,mainExp} = do
  mn <- case mainExp of
          Just (m,t) -> do m' <- unariserExp ddefs [] (Env2 M.empty funEnv) m
                           return $ Just (m', flattenTy t)
          Nothing -> return Nothing
  fds' <- mapM unariserFun fundefs
  return $ Prog ddefs fds' mn


  -- Modifies function to satisfy output invariant (1)
  --
  where
    funEnv = M.map funTy fundefs

    unariserFun :: FunDef3 -> PassM FunDef3
    unariserFun f@FunDef{funTy,funArgs,funBody} = do
      let in_tys  = inTys funTy
          in_tys' = map flattenTy in_tys
          out_ty' = flattenTy (outTy funTy)
          fun_body =
               foldr
                 (\(a,t) acc ->
                    case t of
                      ProdTy{} -> flattenExp a t acc
                      _ -> acc)
                 funBody (zip funArgs in_tys)
          fn = f { funTy = (in_tys', out_ty')
                 , funBody = fun_body }
          env2 = Env2 (M.fromList $ zip  funArgs in_tys) funEnv
      bod <- unariserExp ddefs [] env2 funBody
      return $ fn { funBody = bod }


-- | A projection stack can be viewed as a list of ProjE operations to
-- perform, from left to right.
type ProjStack = [Int]

unariserExp :: DDefs Ty3 -> ProjStack -> Env2 Ty3 -> L Exp3 -> PassM (L Exp3)
unariserExp ddfs stk env2 (L p ex) = L p <$>
  case ex of
    LetE (v,locs,ty,rhs) bod ->
      LetE <$> (v,locs,flattenTy ty,)
           <$> go env2 rhs
           <*> go (extendVEnv v ty env2) bod

    MkProdE es ->
      case stk of
        [] -> flattenProd ddfs stk env2 (l$ ex)
        (ix:s') -> unLoc <$> unariserExp ddfs s' env2 (es ! ix)

    -- When projecting a value out of a nested tuple, we have to update the index
    -- to match the flattened representation. And if the ith projection was a
    -- product before, we have to reconstruct it here, since it will be flattened
    -- after this pass.
    ProjE i e ->
      case unLoc e of
        MkProdE ls -> unLoc <$> go env2 (ls ! i)
        _ -> do
          let ety = gRecoverType ddfs env2 e
              j   = flatProjIdx i ety
              ity = projTy i ety
              fty = flattenTy ity
          e' <- go env2 e
          case unLoc e' of
            MkProdE xs -> return $ unLoc (xs ! j)
            _ ->
             case fty of
               -- reconstruct
               ProdTy tys -> do
                 return $ MkProdE (map (\k -> l$ ProjE k e') [j..(j+(length tys)-1)])
               _ -> return $ ProjE j e'


    -- Straightforward recursion
    --
    VarE{} -> return $ unLoc $ discharge stk (L p ex)

    LitE{} ->
      case stk of
        [] -> return ex
        _  -> error $ "Impossible. Non-empty projection stack on LitE "++show stk

    LitSymE{} ->
      case stk of
        [] -> return ex
        _  -> error $ "Impossible. Non-empty projection stack on LitSymE "++show stk

    AppE v locs args -> unLoc <$> discharge stk <$>
                        (L p <$> AppE v locs <$> mapM (go env2) args)

    PrimAppE pr args -> unLoc <$> discharge stk <$>
                        (L p <$> PrimAppE pr <$> mapM (go env2) args)

    IfE a b c  -> IfE <$> go env2 a <*> go env2 b <*> go env2 c

    CaseE e ls -> do
      -- Add pattern matched vars to the environment
      let f dcon vlocs = extendsVEnv (M.fromList $ zip (map fst vlocs) (lookupDataCon ddfs dcon)) env2
      CaseE <$> go env2 e <*> sequence [ (k,ls',) <$> go (f k ls') x | (k,ls',x) <- ls ]

    DataConE loc dcon args ->
      case stk of
        [] -> unLoc <$> discharge stk <$>
              (L p <$> DataConE loc dcon <$> mapM (go env2) args)
        _  -> error $ "Impossible. Non-empty projection stack on DataConE "++show stk

    TimeIt e ty b -> do
      tmp <- gensym $ toVar "timed"
      e'  <- go env2 e
      return $ LetE (tmp,[],ty, l$ TimeIt e' ty b) (l$ VarE tmp)

    WithArenaE v e -> WithArenaE v <$> go env2 e

    SpawnE v locs args -> unLoc <$> discharge stk <$>
                            (L p <$> SpawnE v locs <$> mapM (go env2) args)

    SyncE -> pure SyncE

    Ext{}  -> return ex
    MapE{}  -> error "unariserExp: MapE TODO"
    FoldE{} -> error "unariserExp: FoldE TODO"

  where
    go = unariserExp ddfs stk

    -- | Reify a stack of projections.
    discharge :: [Int] -> L Exp3 -> L Exp3
    discharge [] e = e
    discharge (ix:rst) (L _ (MkProdE ls)) = discharge rst (ls ! ix)
    discharge (ix:rst) e = discharge rst (l$ ProjE ix e)

    ls ! i = if i <= length ls
             then ls!!i
             else error$ "unariserExp: attempt to project index "++show i++" of list:\n "++sdoc ls


-- | Flatten nested tuples
flattenProd :: DDefs Ty3 -> ProjStack -> Env2 Ty3 -> L Exp3 -> PassM (Exp3)
flattenProd ddfs stk env2 ex =
  case unLoc ex of
    MkProdE{} -> do
      let flat1 = go ex
          tys = L.map (flattenTy . gRecoverType ddfs env2) flat1
      MkProdE <$> go2 tys flat1

    oth -> error $ "flattenProd: Unexpected expression: " ++ sdoc oth
  where
    -- Structural flattening. Just flattens nested MkProdE's
    go :: L Exp3 -> [L Exp3]
    go (L _ (MkProdE js)) = concatMap go js
    go e = [e]

    -- Structural flattening might leave behind some nested tuples.
    -- We flatten them here using type information.
    -- Example: let v = [1,2,3]
    --              w = [v,4]
    --
    -- Here, `w` needs further flattening.
    -- We transform it as:
    --
    -- let v = [1,2,3]
    --     w = [proj 0 v, proj 1 v, proj 2 v, 4]
    --
    go2 :: [Ty3] -> [L Exp3] -> PassM [L Exp3]
    go2 [] [] = return []
    go2 (t:ts) (e:es) =
      case (t,e) of
        (ProdTy tys, L _ VarE{}) -> do
          let fs = [l$ ProjE n e | (_ty,n) <- zip tys [0..]]
          es' <- go2 ts es
          return $ fs ++ es'
        (_ty, L _ ProjE{}) -> do
          e' <- unariserExp ddfs stk env2 e
          es' <- go2 ts es
          return $ [e'] ++ es'
        _ -> ([e] ++) <$> go2 ts es
    go2 ts es = error $ "Unexpected input: " ++ sdoc ts ++ " " ++ sdoc es


-- | Return an updated index for the flattened type
--
-- >>> 1 (ProdTy [ProdTy [IntTy, IntTy, IntTy], IntTy])
-- 3
flatProjIdx :: Int -> Ty3 -> Int
flatProjIdx n ty =
  case ty of
    ProdTy tys ->
      let ProdTy tys' = flattenTy (ProdTy $ take n tys)
      in length tys'
    _ -> error $ "flatProjIdx: non-product type given: " ++ show ty


-- | Flatten nested tuple types.
-- Example:
--
-- ProdTy [IntTy, ProdTy [IntTy, IntTy, IntTy, ProdTy [IntTy, IntTy]]] =>
-- ProdTy [IntTy, IntTy, IntTy, IntTy, IntTy, IntTy]
--
flattenTy :: Ty3 -> Ty3
flattenTy ty =
  case ty of
    ProdTy _ -> ProdTy $ go ty
    _ -> ty
  where go :: Ty3 -> [Ty3]
        go (ProdTy tys) = concatMap go tys
        go ty' = [ty']

-- | Flatten nested tuples in a type-safe way
--
flattenExp :: Var -> Ty3 -> L Exp3 -> L Exp3
flattenExp v ty bod =
  case ty of
    ProdTy _ ->
      let
          -- | Generate projections for non-product types inside a tuple
          --
          -- Examples:
          -- (1) ProdTy [IntTy, ProdTy [IntTy, IntTy, IntTy]] ==
          --     [[0],[1,0],[1,1],[1,2]]
          --
          -- (2) ProdTy [IntTy, ProdTy [IntTy, IntTy, IntTy, ProdTy [IntTy, IntTy]]]
          --     [[0],[1,0],[1,1],[1,2],[1,3,0],[1,3,1]]
          --
          projections :: Ty3 -> ProjStack -> [ProjStack]
          projections (ProdTy tys) acc =
            concatMap (\(ty',i) -> projections ty' (i:acc)) (zip tys [0..])
          projections _ acc = [acc]

          projs = projections ty []
          substs = map (\ps -> (foldr (\i acc -> l$ ProjE i acc) (l$ VarE v) ps,
                                l$ ProjE (sum ps) (l$ VarE v)))
                   projs
          -- FIXME: This is in-efficient because of the substE ?
      in foldr (\(from,to) acc -> substE from to acc) bod substs
    _ -> bod
