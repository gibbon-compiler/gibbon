-- | Infer region multiplicities
--
--   During inference, regions are merely annotated with a region metavariable.
--   InferRegionScope takes the next step and decides the region scope (global/dynamic)
--   and also assigns it a multiplicity.

module Gibbon.Passes.InferRegionScope
  (inferRegScope, inferRegScopeExp) where

import Data.Graph
import qualified Data.Map as M

import Gibbon.DynFlags
import Gibbon.Common
import Gibbon.L2.Syntax

-- All regions are "infinite" right now

-- | Infer region scope and multiplicity for a program annotated with regions
-- and locations.
inferRegScope :: Prog2 -> PassM Prog2
inferRegScope Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM inferRegScopeFun $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just <$> (,ty) <$> inferRegScopeExp mn
  return $ Prog ddefs fundefs' mainExp'

inferRegScopeFun :: FunDef2 -> PassM FunDef2
inferRegScopeFun f@FunDef{funBody} = do
  funBody' <- inferRegScopeExp funBody
  return $ f {funBody = funBody'}

{- Region scoping rules:
~~~~~~~~~~~~~~~~~~~~~~~~

A region in Gibbon can either be global or dynamic (local). Global regions have a
lifetime equal to that of the whole program. Whereas, dynamic regions can be created &
destroyed on the stack. The scope of the values in the region dictate it's scope.
If the value in the region escapes the context it was created in, it has be global.
Otherwise, a dynamic region would be sufficient. Consider two functions of the form:

    fnA = letregion ra in
          letloc la in
          let x = (Leaf 1) at la
          in x

    fnB = letregion rb in
          letloc lb in
          let y = (Leaf 1) at lb
          in 1

The return value of fnA resides in the region `ra`. Therefore `ra` has to be global.
Whereas, it's safe to mark the region `rb` as dynamic. The fn `inferRegScopeExp` traverses
the AST and transforms all region metavariables to fully scoped region variables.

Whenever it encounters a `letregion`, it builds a graph of dependencies of the
relevant part of the AST. And if there's a path between the region and
the end of the AST, the return value so to speak, the region is marked global.
For example, in fnA, it discovers the path `ra -> la -> x` and hence `ra` is global.
In fnB, there's no path from `rb` to 1.

-}

-- | Decide if a region should be global or local (dynamic).
--
--  Dynamic regions are stack allocated and automatically freed
inferRegScopeExp :: Exp2 -> PassM Exp2
inferRegScopeExp ex =
  case ex of
    Ext ext ->
      case ext of
        AddFixed{} -> error "inferRegScopeExp: AddFixed not handled"
        LetRegionE r rhs ->
          case r of
            MMapR{} -> Ext <$> LetRegionE r <$> (go rhs)
            _ ->
              let deps = depList ex
              in case deps of
                   ((retVar,_,_):_) ->
                     let (g,_,vtxF) = graphFromEdges deps
                         regV = regionToVar r
                         -- Vertex of the region variable
                         regVertex =
                           case vtxF regV of
                             Just x  -> x
                             Nothing -> error $ "No vertex for:" ++ sdoc r
                         -- Vertex of the return value
                         retVertex =
                           case vtxF retVar of
                             Just x  -> x
                             Nothing -> error $ "No vertex for:" ++ sdoc retVar
                         -- The value in the region  escapes the current scope if there's
                         -- a path between the region variable and the thing returned.
                         -- TODO: Warn the user when this happens in a fn ?
                     in do dflags <- getDynFlags
                           let defaultMul = if (gopt Opt_BigInfiniteRegions dflags) ||
                                               (gopt Opt_Gibbon1 dflags)
                                            then BigInfinite
                                            else Infinite
                           if path g retVertex regVertex
                           then Ext <$> LetRegionE (GlobR regV defaultMul) <$> (go rhs)
                           -- [2018.03.30] - TEMP: Turning off scoped buffers.
                           -- else Ext$ LetRegionE (DynR regV mul) (inferRegScopeExp rhs)
                           else Ext <$> LetRegionE (GlobR regV defaultMul) <$> (go rhs)
                   [] -> return ex

        -- Straightforward recursion
        LetLocE loc le bod -> Ext <$> LetLocE loc le <$> (go bod)
        RetE{}     -> return ex
        FromEndE{} -> return ex
        BoundsCheck{} -> return ex
        IndirectionE{}-> return ex
        GetCilkWorkerNum -> return ex
        LetAvail vs e    -> Ext <$> LetAvail vs <$> go e

    -- Straightforward recursion ...
    VarE{}     -> return ex
    LitE{}     -> return ex
    LitSymE{}  -> return ex
    AppE{}     -> return ex
    PrimAppE{} -> return ex
    DataConE{} -> return ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> (IfE a) <$> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    LetE (v,locs,ty,rhs) bod -> LetE <$> (v,locs,ty,) <$> go rhs <*> go bod
    CaseE scrt mp -> (CaseE scrt) <$> mapM (\(a,b,c) -> (a,b,) <$> go c) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{} -> pure ex
    SyncE{}  -> pure ex
    IsBigE{} -> pure ex
    WithArenaE v e -> WithArenaE v <$> go e
    MapE{}  -> error $ "inferRegScopeExp: TODO MapE"
    FoldE{} -> error $ "inferRegScopeExp: TODO FoldE"
  where
    go = inferRegScopeExp
