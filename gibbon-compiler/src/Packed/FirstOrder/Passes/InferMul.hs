{-# LANGUAGE OverloadedStrings #-}


-- | Infer region multiplicities
--
--   During inference, regions are merely annotated with a region metavariable.
--   InferMul takes the next step and decides the region scope (global/dynamic)
--   and also assigns it a multiplicity.

module Packed.FirstOrder.Passes.InferMul
  (inferMul, inferRegScope) where

import Data.Loc
import Data.Graph
import qualified Data.Map as M

import Packed.FirstOrder.Common hiding (FunDef(..))
import Packed.FirstOrder.L1.Syntax hiding (Prog(..), FunDef(..))
import Packed.FirstOrder.L2.Syntax as L2

-- All regions are "infinite" right now

-- | Infer multiplicity for a program annotated with regions & locations
inferMul :: L2.Prog -> SyM L2.Prog
inferMul Prog{ddefs,fundefs,mainExp} = do
  let fds' = map inferMulFn $ M.elems fundefs
      fundefs' = M.fromList $ map (\f -> (funname f,f)) fds'
      mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (mn, ty) -> Just (inferRegScope mn,ty)
  return $ Prog ddefs fundefs' mainExp'

inferMulFn :: L2.FunDef -> L2.FunDef
inferMulFn f@FunDef{funbod} = f {funbod = inferRegScope funbod}

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
Whereas, it's safe to mark the region `rb` as dynamic. The fn `inferRegScope` traverses
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
inferRegScope :: L L2.Exp2 -> L L2.Exp2
inferRegScope (L p ex) = L p $
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
                    then Ext$ LetRegionE (GlobR regV Infinite) (inferRegScope rhs)
                    -- [2018.03.30] - TEMP: Turning off scoped buffers.
                    -- else Ext$ LetRegionE (DynR regV Infinite) (inferRegScope rhs)
                    else Ext$ LetRegionE (GlobR regV Infinite) (inferRegScope rhs)
               [] -> ex

        -- Straightforward recursion
        LetLocE loc le bod -> Ext $ LetLocE loc le (inferRegScope bod)
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
    ProjE i e  -> ProjE i (inferRegScope e)
    IfE a b c  -> IfE a (inferRegScope b) (inferRegScope c)
    MkProdE ls -> MkProdE $ map inferRegScope ls
    LetE (v,locs,ty,rhs) bod -> LetE (v,locs,ty, inferRegScope rhs) (inferRegScope bod)
    CaseE scrt mp -> CaseE scrt $ map (\(a,b,c) -> (a,b, inferRegScope c)) mp
    TimeIt e ty b -> TimeIt (inferRegScope e) ty b
    MapE{}  -> error $ "inferRegScope: TODO MapE"
    FoldE{} -> error $ "inferRegScope: TODO FoldE"
