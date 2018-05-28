{-# LANGUAGE OverloadedStrings #-}


-- | Infer region multiplicities
--
--   During inference, regions are merely annotated with a region metavariable.
--   InferMultiplicity takes the next step and decides the region scope (global/dynamic)
--   and also assigns it a multiplicity.

module Gibbon.Passes.InferMultiplicity
  (inferRegScope, inferRegScopeExp) where

import Data.Loc
import Data.Graph
import qualified Data.Map as M

import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L2.Syntax as L2

-- All regions are "infinite" right now

-- | Infer multiplicity for a program annotated with regions & locations
inferRegScope :: Multiplicity -> L2.Prog2 -> PassM L2.Prog2
inferRegScope mul Prog{ddefs,fundefs,mainExp} = do
  let fds' = map (inferRegScopeFun mul) $ M.elems fundefs
      fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (mn, ty) -> Just (inferRegScopeExp mul mn,ty)
  return $ Prog ddefs fundefs' mainExp'

inferRegScopeFun :: Multiplicity -> L2.FunDef2 -> L2.FunDef2
inferRegScopeFun mul f@FunDef{funBody} = f {funBody = inferRegScopeExp mul funBody}

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
inferRegScopeExp :: Multiplicity -> L L2.Exp2 -> L L2.Exp2
inferRegScopeExp mul (L p ex) = L p $
  case ex of
    Ext ext ->
      case ext of
        LetRegionE r rhs ->
          let deps = depList (L p ex)
          in case deps of
               ((retVar,_,_):_) ->
                 let (g,_,vtxF) = graphFromEdges deps
                     regV = regionVar r
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
                 in if path g retVertex regVertex
                    then Ext$ LetRegionE (GlobR regV mul) (go rhs)
                    -- [2018.03.30] - TEMP: Turning off scoped buffers.
                    -- else Ext$ LetRegionE (DynR regV mul) (inferRegScopeExp rhs)
                    else Ext$ LetRegionE (GlobR regV mul) (go rhs)
               [] -> ex

        -- Straightforward recursion
        LetLocE loc le bod -> Ext $ LetLocE loc le (go bod)
        RetE{}     -> Ext ext
        FromEndE{} -> Ext ext
        BoundsCheck{} -> Ext ext
        IndirectionE{}-> Ext ext

    -- Straightforward recursion ...
    VarE{}     -> ex
    LitE{}     -> ex
    LitSymE{}  -> ex
    AppE{}     -> ex
    PrimAppE{} -> ex
    DataConE{} -> ex
    ProjE i e  -> ProjE i (go e)
    IfE a b c  -> IfE a (go b) (go c)
    MkProdE ls -> MkProdE $ map go ls
    LetE (v,locs,ty,rhs) bod -> LetE (v,locs,ty, go rhs) (go bod)
    CaseE scrt mp -> CaseE scrt $ map (\(a,b,c) -> (a,b, go c)) mp
    TimeIt e ty b -> TimeIt (go e) ty b
    MapE{}  -> error $ "inferRegScopeExp: TODO MapE"
    FoldE{} -> error $ "inferRegScopeExp: TODO FoldE"
  where
    go = inferRegScopeExp mul
