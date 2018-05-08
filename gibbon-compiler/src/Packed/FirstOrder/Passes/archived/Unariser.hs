{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-- | Eliminate tuples except under special circumstances expected by
-- Lower.

-- WARNING: seeded with DUPLICATED code from InlinePacked

module Packed.FirstOrder.Passes.Unariser
  (unariser) where

import Data.Loc
import qualified Data.Map as M

import Packed.FirstOrder.Common hiding (FunDef, FunDefs)
import Packed.FirstOrder.L1.Syntax hiding (FunDef, Prog(..))
import Packed.FirstOrder.L3.Syntax

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
unariser :: Prog -> SyM Prog
unariser prg = do
  prg' <- mapMExprs unariserExp prg
  return prg'{fundefs = M.map unariserFun (fundefs prg')}


-- | A projection stack can be viewed as a list of ProjE operations to
-- perform, from left to right.
type ProjStack = [Int]


-- | Maps variables onto tuples of (projections of) other variables
type Env = [(Var,[(ProjStack,Var)])]


-- | Modifies function to satisfy output invariant (1)
--
unariserFun :: FunDef -> FunDef
unariserFun f@FunDef{funty,funarg,funbod} =
  case inT of
    ProdTy _ ->
      let ty  = flattenTy inT
          bod = flattenExp funarg inT funbod
      in f{funbod = bod, funty = funty{arrIn = ty, arrOut = flattenTy outT}}
    _ -> f
  where inT = arrIn funty
        outT = arrOut funty


-- | Take an ignored argument to match mapMExprs' conventions.
--
-- In the recursive "go" worker here, we maintain:
--   (1) pending projections that enclose our current context, and
--   (2) a map from variable bindings with tuple type, to
--       finer-grained bindings to individual components.
--
unariserExp :: ignored -> L Exp3 -> SyM (L Exp3)
unariserExp _ = go [] []
  where
  var v = v
  l ! i = if i <= length l
          then l!!i
          else error$ "unariserExp: attempt to project index "++show i++" of list:\n "++sdoc l

  -- | Reify a stack of projections.
  discharge :: [Int] -> L Exp3 -> L Exp3
  discharge [] e = e
  discharge (ix:rst) (L _ (MkProdE ls)) = discharge rst (ls ! ix)
  discharge (ix:rst) e = discharge rst (l$ ProjE ix e)

  flattenProd :: L Exp3 -> [L Exp3]
  flattenProd (L _ (MkProdE es)) = concatMap flattenProd es
  flattenProd e = [e]

  mkLet :: (Var, Ty3, L Exp3) -> L Exp3 -> L Exp3
  mkLet (v,t,L p (LetE (v2,locs,t2,rhs2) bod1)) bod2 = L p $ LetE (v2,locs,t2,rhs2) $
                                                       l$ LetE (v,[],t,bod1) bod2
  mkLet (v,t,rhs) bod = l$ LetE (v,[],t,rhs) bod

  -- FIXME: need to track full expr binds like InlineTrivs
  -- Or do we?  Not clear yet.
  go :: ProjStack -> Env -> L Exp3 -> SyM (L Exp3)
  go stk env (L p e0) =
    dbgTrace 7 ("Unariser processing with stk "++
             ndoc stk++", env: "++ndoc env++"\n exp: "++sdoc e0) $
    case e0 of
      (MkProdE es) -> case stk of
                        (ix:s') -> go s' env (es ! ix)
                        [] -> L p <$> MkProdE <$> mapM (go stk env) (concatMap flattenProd es)

      -- (ProjE ix (VarE v)) -> discharge stk <$> -- Danger.
      --                        case lookup v env of
      --                          Just vs -> pure$ let (stk,v') = vs ! ix in
      --                                           applyProj (ix:stk, v')
      --                          Nothing -> pure$ VarE v -- This must be one that Lower can handle.
      (ProjE i e)  -> go (i:stk) env e  -- Push a projection inside lets or conditionals.

      (VarE v) -> case lookup v env of
                  Nothing -> pure$ discharge stk $ l$ VarE (var v)
                  -- Reprocess after substituting in case they were not terminal after all:a
                  -- Works for var-to-var aliases.
                  Just vs -> go stk env (mkProd (map applyProj vs))

      LetE (vr,_locs,ty, L _p (CaseE scrt ls)) bod | isCheap bod ->
        go stk env $ l $
           CaseE scrt [ (k,vs, mkLet (vr,ty,e) bod)
                      | (k,vs,e) <- ls]

      -- Flatten so that we can see what's stopping us from unzipping:
      LetE (v1,locs,t1, L p2 (LetE (v2,locs2,t2,rhs2) rhs1)) bod ->
        go stk env $ L p2 $ LetE (v2,locs2,t2,rhs2) $ L p $ LetE (v1,locs,t1,rhs1) bod

      -- TEMP: HACK/workaround.  See FIXME .
      -- LetE (v1,ProdTy _,rhs@LetE{})  (ProjE ix (VarE v2)) | v1 == v2 -> go (ix:stk) env rhs
      LetE (v1,_locs1,ProdTy _,rhs@(L _ CaseE{})) (L _ (ProjE ix (L _ (VarE v2)))) | v1 == v2 ->
        go (ix:stk) env rhs

      {-
      This is causing problems with the buildTreeSumProg example. It's not able
      to properly flatten the packed tuple in the tail position (return value).
      I couldn't fix this easily. Commenting this works out for now.

      LetE (vr,_locs,ProdTy tys, L _ (MkProdE ls)) bod -> do
        vs <- sequence [ gensym (toVar "unzip") | _ <- ls ]
        let -- Here's a little bit of extra complexity to NOT introduce var/var copies:
            (mbinds,substs) = unzip
                              [ case projOfVar e of
                                  Just pr -> (Nothing, pr)
                                  Nothing -> (Just (v,[],t,e), ([],v))
                              | (v,t,e) <- (zip3 vs tys ls) ]
            binds = catMaybes mbinds
            env' = (vr, substs):env
        -- Here we *reprocess* the results in case there is more unzipping to do:
        go stk env' $ mkLets binds bod

      -- Bulk copy prop, WRONG:
      -- (LetE (v1,ProdTy tys, VarE v2) bod) ->
      --     case lookup v2 env of
      --       Just vs -> go stk env $ LetE (v1,ProdTy tys, MkProdE (map VarE vs)) bod
      --       Nothing -> go stk ((v1,[v2]):env) bod -- Copy-

      -- More nuanced copy-prop:
      LetE (v1,_locs,ProdTy tys, proj) bod | Just (stk2,v2) <- projOfVar proj ->
         let env' = buildAliases (v1,tys) (stk2,v2) env
         in go stk env' bod
      -- case lookup v2 env of
      --   Just vs -> go stk env $ LetE (v1,ProdTy tys, MkProdE (map VarE vs)) bod
      --   -- This is problematic:
      --   -- Nothing -> go stk ((v1,[v2]):env) bod -- Copy-prop
      --   Nothing -> LetE <$> ((v1,ProdTy tys) <$> go [] proj) <*>
      --                 go stk ((v1,Nothing):env) bod
      -}

      -- A stupid copy-prop for a corner case
      -- TODO: change this
      LetE (v,_locs,ProdTy{},rhs@(L _ ProjE{})) bod -> do
        let bod' = substE (l$ VarE v) rhs bod
        go stk env bod'

      -- And this is a HACK.  Need a more general solution:
      LetE (v,locs,ty@ProdTy{}, rhs@(L _ (TimeIt{}))) bod ->
        fmap (L p) $ LetE <$> ((v,locs,ty,) <$> go [] env rhs) <*> go stk env bod


      LetE (v,locs,ty@(ProdTy _), rhs) bod -> do
        dbgTrace 5 ("[unariser] flattening " ++ show e0) return()
        rhs' <- go [] env rhs
        -- ty'  <- tyWithFreshLocs ty -- convert L1.Ty -> L2.Ty
        bod' <- go stk env bod
        let ty''  = flattenTy ty
            bod'' = flattenExp v ty bod'
        -- stripTyLocs converts L2.Ty -> L1.Ty
        return $ (L p) $ LetE (v, locs, ty'', rhs') bod''

      -- Straightforward recursion for all the remaining cases

      LetE (v,locs,t,rhs) e ->
        fmap (L p) $ LetE <$> ((v,locs,t,) <$> go [] env rhs) <*> (go stk env e)

      LitE i | [] <- stk -> pure$ (L p)$ LitE i
             | otherwise -> error $ "Impossible. Non-empty projection stack on LitE "++show stk
      LitSymE v | [] <- stk -> pure $ (L p)$ LitSymE v
                | otherwise -> error $ "Impossible. Non-empty projection stack on LitSymE "++show stk

      PrimAppE pr es -> discharge stk <$>
                          (L p) <$> PrimAppE pr <$> mapM (go stk env) es

      -- TODO: these need to be handled by lower to become varrefs into a multi-valued return.
      AppE f locs e  -> discharge stk <$> (L p <$> AppE f locs <$> go [] env e)


      IfE e1 e2 e3 -> fmap (L p) $
        IfE <$> go [] env e1 <*> go stk env e2 <*> go stk env e3

      CaseE e ls -> fmap (L p) $
                        CaseE <$> go [] env e <*>
                        sequence [ (k,ls',) <$> go stk env x
                                 | (k,ls',x) <- ls ]

      DataConE c loc es
        | [] <- stk -> fmap (L p) $ DataConE c loc <$> mapM (go [] env) es
        | otherwise -> error $ "Impossible. Non-empty projection stack on DataConE: "++show stk

      TimeIt e ty b -> do
        -- Put this in the form Lower wants:
        tmp <- gensym $ toVar "timed"
        e' <- go stk env e
        return $ (L p) $ LetE (tmp,[],ty, l$ TimeIt e' ty b) (l$ VarE tmp)

      -- We know that this would be trivial. We can revisit this later
      Ext _ext -> return $ L p e0

      MapE{}  -> error "FINISHLISTS"
      FoldE{} -> error "FINISHLISTS"
      -- (MapE (v,t,e') e) -> let env' = (v,Nothing) : env in
      --                      MapE (var v,t,go stk env e') (go stk env' e)
      -- (FoldE (v1,t1,e1) (v2,t2,e2) e3) ->
      --      let env' = (v1,Nothing) : (v2,Nothing) : env in
      --      FoldE (var v1,t1,go stk env e1) (var v2,t2,go stk env e2)
      --            (go stk env' e3)

isCheap :: L Exp3 -> Bool
isCheap _ = True


applyProj :: (ProjStack,Var) -> L Exp3
applyProj (stk,v) = go stk (l$ VarE v)
  where
    go [] e     = e
    go (i:is) e = go is (l$ ProjE i e)


projOfVar :: L Exp3 -> Maybe (ProjStack, Var)
projOfVar = lp []
 where
   lp stk (L _ (VarE v))    = Just (stk,v)
   lp stk (L _ (ProjE i e)) = lp (i:stk) e
   lp _   _                 = Nothing

-- | Binnd v1 to a projection of v2 in the current environment.
buildAliases :: (Var,[Ty3]) -> (ProjStack, Var) -> Env -> Env
buildAliases (v1,tys) (stk,v2) env =
  let maxIx = length tys - 1 in
  let new = case lookup v2 env of
             -- We cannot inline v2, it must come from a function return or something.
             -- So instead we can still unzip ourselves, and reference v2.
             Nothing -> ( v1, [ ([ix],v2) | ix <- [0..maxIx] ] )
             -- When we get a hit, we expect it to have the right number of entries:
             Just hits ->
                 -- We are bound to a PROJECTION of v2, so combine stk with what's already there.
                 (v1, [ (s ++ stk, v')
                      | (_ix,(s,v')) <- fragileZip [0..maxIx] hits ])
  in dbgTrace 5 (" [unariser] Extending environment with these mappings: "++show new) $
     new : env


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
