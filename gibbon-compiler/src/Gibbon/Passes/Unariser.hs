module Gibbon.Passes.Unariser
  (unariser, unariserExp) where

import qualified Data.Map as M
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L3.Syntax
import Gibbon.Passes.Flatten()


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
-- [Aditya Gupta, Oct 2021]
-- NOTE: I am limiting flattening to only intermediate expressions. i.e. the tail value
-- of main expression is a terminal expression and shouldn't be flattened.
-- We can recursively propagate terminality based on expression type. This way all intermediate
-- expressions will enjoy benefit from flattening, but we still retain same output for terminal expressions.
-- We can have a separate function to recover after unarising but that won't have the env2/ddefs values
-- and we won't be able to fuse it into unariser cases. But on the other hands, defining a separate function
-- can eliminate missed cases, but there are only few, so combining recovering terminal expressions in unariser
-- seems best.

unariser :: Prog3 -> PassM Prog3
unariser Prog{ddefs,fundefs,mainExp} = do
  mn <- case mainExp of
          -- type should remain same and main output is a terminal expression
          Just (m,t) -> do m' <- unariserExp True ddefs [] (Env2 M.empty funEnv) m
                           return $ Just (m', t)
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
      -- all function bodies are intermediate expressions
      bod <- unariserExp False ddefs [] env2 funBody
      return $ fn { funBody = bod }


-- | A projection stack can be viewed as a list of ProjE operations to
-- perform, from left to right.
type ProjStack = [Int]

unariserExp :: Bool -> DDefs Ty3 -> ProjStack -> Env2 Ty3 -> Exp3 -> PassM Exp3
unariserExp isTerminal ddfs stk env2 ex =
  case ex of
    LetE (v,locs,ty,rhs) bod ->
      LetE . (v,locs, flattenTy ty,)
        <$> go False env2 rhs
        <*> go isTerminal (extendVEnv v ty env2) bod

    MkProdE es ->
      -- if terminal, don't flatten product
      if isTerminal then pure $ recover0 ex else
        case stk of
          [] -> flattenProd ddfs stk env2 ex
          (ix:s') -> unariserExp False ddfs s' env2 (es ! ix)

    -- When projecting a value out of a nested tuple, we have to update the index
    -- to match the flattened representation. And if the ith projection was a
    -- product before, we have to reconstruct it here, since it will be flattened
    -- after this pass.
    --
    -- if it's a terminal expression, then ith projection should be a terminal,
    -- we can reuse reconstruciton logic.
    ProjE i e ->
      case e of
        MkProdE ls -> go isTerminal env2 (ls ! i)
        _ -> do
          let ety = gRecoverType ddfs env2 e -- type before flattening
              j   = flatProjIdx i ety -- index in flattened type
              ity = projTy i ety -- ith index type before flattening
              fty = flattenTy ity -- jth index type in flattened
          e' <- go False env2 e -- recusrively unarise, but since this is an intermediate value, we can flatten it
          case e' of
            -- if we get a product after flattening, get jth element of flattened element
            MkProdE xs -> return (xs ! j)
            _ ->
              -- otherwise, check jth element
             case fty of
               -- reconstruct, in case of nested tuple (whether terminal or not)
               ProdTy tys -> do
                 return $ MkProdE (map (\k -> ProjE k e') [j..(j+length tys-1)])
               -- if not a tuple, take projection
               _ -> return $ ProjE j e'


    -- Straightforward recursion
    VarE{} -> return . (if isTerminal then recover0 else id) $ discharge stk ex

    LitE{} ->
      case stk of
        [] -> return ex
        _  -> error $ "Impossible. Non-empty projection stack on LitE "++show stk

    CharE{} ->
      case stk of
        [] -> return ex
        _  -> error $ "Impossible. Non-empty projection stack on LitE "++show stk

    FloatE{} ->
      case stk of
        [] -> return ex
        _  -> error $ "Impossible. Non-empty projection stack on LitE "++show stk

    LitSymE{} ->
      case stk of
        [] -> return ex
        _  -> error $ "Impossible. Non-empty projection stack on LitSymE "++show stk

    -- For function output, we need to recover the application nto the arguments
    AppE v locs args -> do
      exp0 <- discharge stk <$> (AppE v locs <$> mapM (go False env2) args)
      if isTerminal
        then do
          tmp <- gensym "tmp_app"
          let ty' = gRecoverType ddfs env2 exp0
          return $ LetE (tmp, [], flattenTy ty', exp0) (recover (VarE tmp) ty')
        else
          pure exp0

    PrimAppE pr args -> discharge stk <$> (PrimAppE pr <$> mapM (go False env2) args)

    -- condition is an intermediate expression, we only care about then and else branches as terminal expressions
    IfE a b c  -> IfE <$> go False env2 a <*> go isTerminal env2 b <*> go isTerminal env2 c

    CaseE e ls -> do
      -- Add pattern matched vars to the environment
      -- data constructor arguments are also terminal
      let f dcon vlocs = extendsVEnv (M.fromList $ zip (map fst vlocs) (lookupDataCon ddfs dcon)) env2
      CaseE <$> go False env2 e <*> sequence [ (k,ls',) <$> go isTerminal (f k ls') x | (k,ls',x) <- ls ]

    DataConE loc dcon args ->
      case stk of
        -- data constructor arguments are also terminal
        [] -> discharge stk <$>
              (DataConE loc dcon <$> mapM (go False env2) args)
        _  -> error $ "Impossible. Non-empty projection stack on DataConE "++show stk

    TimeIt e ty b -> do
      tmp <- gensym $ toVar "timed"
      e'  <- go isTerminal env2 e
      return $ LetE (tmp,[],flattenTy ty, TimeIt e' ty b) (VarE tmp)

    WithArenaE v e -> WithArenaE v <$> go isTerminal env2 e

    SpawnE v locs args -> discharge stk <$>
                            (SpawnE v locs <$> mapM (go False env2) args)

    SyncE -> pure SyncE

    Ext (RetE ls) -> do
      (MkProdE ls1) <- go isTerminal env2 (MkProdE ls)
      pure $ Ext $ RetE ls1

    Ext (LetAvail vs bod) -> do
        bod' <- go isTerminal env2 bod
        return$ Ext $ LetAvail vs bod'
    Ext{}   -> return ex
    MapE{}  -> error "unariserExp: MapE TODO"
    FoldE{} -> error "unariserExp: FoldE TODO"

  where
    go isTerminal' = unariserExp isTerminal' ddfs stk

    -- | Reify a stack of projections.
    discharge :: [Int] -> Exp3 -> Exp3
    discharge [] e = e
    discharge (ix:rst) ((MkProdE ls)) = discharge rst (ls ! ix)
    discharge (ix:rst) e = discharge rst (ProjE ix e)

    recover0 ex0 = let ty = gRecoverType ddfs env2 ex0 in recover ex0 ty
    recover :: Exp3 -> Ty3 -> Exp3
    recover ex0 (ProdTy tys) =
      mkProd . fst $ recover' 0 ex0 tys
    recover ex0 _ = ex0
    recover' :: Int -> Exp3 -> [Ty3] -> ([Exp3], Int)
    recover' idx _ [] = ([], idx)
    recover' _ ex0@(MkProdE xs) tys =
      if length xs == length tys then (zipWith recover xs tys, undefined)
      else error $ "recover': unmatched expression " ++ sdoc ex0 ++ " for type " ++ sdoc tys
    recover' idx ex0 (ty:tys)=
      case ty of
        ProdTy tys' ->
          let (res, idx') = recover' idx ex0 tys'
              (res', idx'') = recover' idx' ex0 tys
          in  (mkProd res:res', idx'')
        _ ->
          let (res, idx') = recover' (idx+1) ex0 tys
          in  (mkProj idx ex0:res, idx')


    ls ! i = if i <= length ls
             then ls!!i
             else error$ "unariserExp: attempt to project index "++show i++" of list:\n "++sdoc ls


-- | Flatten nested tuples
flattenProd :: DDefs Ty3 -> ProjStack -> Env2 Ty3 -> Exp3 -> PassM Exp3
flattenProd ddfs stk env2 ex =
  case ex of
    MkProdE{} -> do
      let flat1 = go ex
          tys = L.map (flattenTy . gRecoverType ddfs env2) flat1
      MkProdE <$> go2 tys flat1

    oth -> error $ "flattenProd: Unexpected expression: " ++ sdoc oth
  where
    -- Structural flattening. Just flattens nested MkProdE's
    go :: Exp3 -> [Exp3]
    go ((MkProdE js)) = concatMap go js
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
    go2 :: [Ty3] -> [Exp3] -> PassM [Exp3]
    go2 [] [] = return []
    go2 (t:ts) (e:es) =
      case (t,e) of
        (ProdTy tys, VarE{}) -> do
          let fs = [ProjE n e | (_ty,n) <- zip tys [0..]]
          es' <- go2 ts es
          return $ fs ++ es'
        (_ty, ProjE{}) -> do
          e' <- unariserExp False ddfs stk env2 e
          es' <- go2 ts es
          return $ e': es'
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
flattenExp :: Var -> Ty3 -> Exp3 -> Exp3
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
          substs = map (\ps -> (foldr ProjE (VarE v) ps,
                                ProjE (sum ps) (VarE v)))
                   projs
          -- FIXME: This is in-efficient because of the substE ?
      in foldr (\(from,to) acc -> substE from to acc) bod substs
    _ -> bod