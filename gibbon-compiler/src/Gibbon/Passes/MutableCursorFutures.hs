{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

-- | Repair mutable-cursor L3 after cursorization.
--
-- Cursorize still owns the source-level translation. This pass is deliberately
-- smaller: it works over the already cursorized L3 let-chain and repairs places
-- where a temporary cursor-array is used as a mutable output cursor for a call.
-- In that shape, the callee mutates the temporary in place, so the owning
-- mutable cursor-array must be updated from it before later code reads the
-- owner as the current cursor state.
module Gibbon.Passes.MutableCursorFutures
  ( repairMutableCursorFutures
  ) where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3

type Bind3 = (Var, [()], L3.Ty3, L3.Exp3)

data CursorArrayCopy = CursorArrayCopy Var Var L3.Ty3
  deriving (Eq, Ord, Show)

data MutableCallShape =
  MutableCallShape
    { mcsOutputEndIx :: Int
    , mcsOutputCurrentIx :: Int
    , mcsCursorArrayTy :: L3.Ty3
    }
  deriving (Eq, Ord, Show)

type FunShapes = M.Map Var MutableCallShape

repairMutableCursorFutures :: L3.Prog3 -> PassM L3.Prog3
repairMutableCursorFutures prog@Prog{fundefs, mainExp} = do
  let funShapes = M.mapMaybe mutableCallShape fundefs
  fds_p <- mapM (repairFun funShapes) (M.elems fundefs)
  mainExp_p <- mapM (\(e, ty) -> (,ty) <$> repairExp funShapes e) mainExp
  pure $
    prog
      { fundefs = M.fromList [ (funName f, f) | f <- fds_p ]
      , mainExp = mainExp_p
      }

repairFun :: FunShapes -> L3.FunDef3 -> PassM L3.FunDef3
repairFun funShapes fn@FunDef{funBody} = do
  let env0 = M.fromList $ zip (funArgs fn) (fst $ funTy fn)
  funBody_p <- repairExpWith funShapes env0 funBody
  pure fn { funBody = funBody_p }

repairExp :: FunShapes -> L3.Exp3 -> PassM L3.Exp3
repairExp funShapes = repairExpWith funShapes M.empty

repairExpWith :: FunShapes -> M.Map Var L3.Ty3 -> L3.Exp3 -> PassM L3.Exp3
repairExpWith funShapes env ex0 = do
  (binds, tailExp) <- repairLets funShapes env ex0
  pure $ L3.mkLets binds tailExp

repairLets :: FunShapes -> M.Map Var L3.Ty3 -> L3.Exp3 -> PassM ([Bind3], L3.Exp3)
repairLets funShapes env ex =
  case ex of
    L3.LetE (v, locs, ty, rhs) bod -> do
      rhs_p <- repairNested funShapes env rhs
      let env_p = M.insert v ty env
      (bodBinds, tailExp) <- repairLets funShapes env_p bod
      post <- postCallInstalls funShapes env rhs_p
      pure ((v, locs, ty, rhs_p) : post ++ bodBinds, tailExp)
    _ -> ([],) <$> repairNested funShapes env ex

repairNested :: FunShapes -> M.Map Var L3.Ty3 -> L3.Exp3 -> PassM L3.Exp3
repairNested funShapes env ex =
  case ex of
    L3.IfE a b c ->
      L3.IfE <$> repairExpWith funShapes env a
             <*> repairExpWith funShapes env b
             <*> repairExpWith funShapes env c
    L3.CaseE scrt brs ->
      L3.CaseE <$> repairExpWith funShapes env scrt
               <*> mapM (\(dc, vars, rhs) -> (dc, vars,) <$> repairExpWith funShapes env rhs) brs
    L3.MkProdE ls -> L3.MkProdE <$> mapM (repairExpWith funShapes env) ls
    L3.ProjE i e -> L3.ProjE i <$> repairExpWith funShapes env e
    L3.PrimAppE p args -> L3.PrimAppE p <$> mapM (repairExpWith funShapes env) args
    L3.TimeIt e ty b -> L3.TimeIt <$> repairExpWith funShapes env e <*> pure ty <*> pure b
    L3.WithArenaE v e -> L3.WithArenaE v <$> repairExpWith funShapes env e
    L3.SpawnE fn locs args -> L3.SpawnE fn locs <$> mapM (repairExpWith funShapes env) args
    L3.MapE (v, ty, rhs) bod ->
      L3.MapE <$> ((v, ty,) <$> repairExpWith funShapes env rhs)
              <*> repairExpWith funShapes (M.insert v ty env) bod
    L3.FoldE (v1, ty1, rhs1) (v2, ty2, rhs2) bod ->
      L3.FoldE
        <$> ((v1, ty1,) <$> repairExpWith funShapes env rhs1)
        <*> ((v2, ty2,) <$> repairExpWith funShapes env rhs2)
        <*> repairExpWith funShapes (M.insert v1 ty1 (M.insert v2 ty2 env)) bod
    L3.DataConE loc dc args -> L3.DataConE loc dc <$> mapM (repairExpWith funShapes env) args
    L3.Ext ext -> L3.Ext <$> repairExt funShapes env ext
    _ -> pure ex

repairExt :: FunShapes -> M.Map Var L3.Ty3 -> L3.E3Ext () L3.Ty3 -> PassM (L3.E3Ext () L3.Ty3)
repairExt funShapes env ext =
  case ext of
    L3.ForE idx bound bod ->
      L3.ForE idx <$> repairExpWith funShapes env bound
                  <*> repairExpWith funShapes (M.delete idx env) bod
    L3.WhileCursor cur bod -> L3.WhileCursor cur <$> repairExpWith funShapes env bod
    L3.WhileCursorEnd cur end bod -> L3.WhileCursorEnd cur end <$> repairExpWith funShapes env bod
    L3.WriteScalar s cur rhs -> L3.WriteScalar s cur <$> repairExpWith funShapes env rhs
    L3.WriteTagPacked cur rhs -> L3.WriteTagPacked cur <$> repairExpWith funShapes env rhs
    L3.WriteTaggedCursor cur rhs -> L3.WriteTaggedCursor cur <$> repairExpWith funShapes env rhs
    L3.WriteCursorMutable cur rhs -> L3.WriteCursorMutable cur <$> repairExpWith funShapes env rhs
    L3.WriteList cur rhs ty -> (\rhs_p -> L3.WriteList cur rhs_p ty) <$> repairExpWith funShapes env rhs
    L3.WriteVector cur rhs ty -> (\rhs_p -> L3.WriteVector cur rhs_p ty) <$> repairExpWith funShapes env rhs
    L3.AddCursor cur rhs -> L3.AddCursor cur <$> repairExpWith funShapes env rhs
    L3.BumpCursorMutable cur rhs -> L3.BumpCursorMutable cur <$> repairExpWith funShapes env rhs
    L3.AddrOfCursor rhs -> L3.AddrOfCursor <$> repairExpWith funShapes env rhs
    L3.LetAvail vars bod -> L3.LetAvail vars <$> repairExpWith funShapes env bod
    L3.Assert rhs -> L3.Assert <$> repairExpWith funShapes env rhs
    L3.WriteCursorSelectiveIndirection cur target end mask ->
      L3.WriteCursorSelectiveIndirection cur target end <$> repairExpWith funShapes env mask
    _ -> pure ext

postCallInstalls :: FunShapes -> M.Map Var L3.Ty3 -> L3.Exp3 -> PassM [Bind3]
postCallInstalls funShapes env rhs =
  case rhs of
    L3.AppE fn _ _ args ->
      concat <$> mapM installForCopyCandidate (callCursorArrayCopies funShapes env fn args)
    _ -> pure []

callCursorArrayCopies :: FunShapes -> M.Map Var L3.Ty3 -> Var -> [L3.Exp3] -> [CursorArrayCopy]
callCursorArrayCopies funShapes env fn args =
  case M.lookup fn funShapes of
    Just MutableCallShape{mcsOutputEndIx, mcsOutputCurrentIx, mcsCursorArrayTy} ->
      copyFromIxs (Just mcsCursorArrayTy) mcsOutputEndIx mcsOutputCurrentIx
    Nothing ->
      case cursorArrayArgVars of
        -- Fully factored mutable producer/transformer calls have this shape at
        -- the call site even when the function type has been simplified enough
        -- that the shape table misses it:
        -- input ends, output owner/end, output current, input current.
        (_ : (outEndIx, _, ty) : (outCurIx, _, _) : _ : _) ->
          copyFromIxs (Just ty) outEndIx outCurIx
        _ -> []
  where
    argVarAt fallbackTy ix =
      case drop ix args of
        L3.VarE v : _ ->
          case M.lookup v env of
            Just ty | isCursorArrayTy ty -> Just (v, ty)
            _ -> (v,) <$> fallbackTy
        _ -> Nothing

    cursorArrayArgVars =
      [ (ix, v, ty)
      | (ix, L3.VarE v) <- zip [0..] args
      , Just ty <- [M.lookup v env]
      , isCursorArrayTy ty
      ]

    copyFromIxs fallbackTy outEndIx outCurIx =
      case (argVarAt fallbackTy outEndIx, argVarAt fallbackTy outCurIx) of
        (Just (dst, _), Just (src, ty))
          | dst /= src -> [CursorArrayCopy dst src ty]
        _ -> []

mutableCallShape :: L3.FunDef3 -> Maybe MutableCallShape
mutableCallShape FunDef{funTy} =
  case cursorArrayArgs (fst funTy) of
    -- Fully factored mutable producer/transformer calls pass:
    -- input ends, output ends, output current, input current.
    -- Some function types retain additional cursor arrays, so the mutable
    -- producer shape is the leading four cursor-array arguments.
    (_ : (outEndIx, _) : (outCurIx, outCurTy) : _ : _) ->
      Just (MutableCallShape outEndIx outCurIx outCurTy)
    _ -> Nothing

cursorArrayArgs :: [L3.Ty3] -> [(Int, L3.Ty3)]
cursorArrayArgs tys =
  [ (ix, ty) | (ix, ty) <- zip [0..] tys, isCursorArrayTy ty ]

installForCopyCandidate :: CursorArrayCopy -> PassM [Bind3]
installForCopyCandidate (CursorArrayCopy dst src ty) = do
  void <- gensym "install_future_cursor"
  pure [(void, [], L3.ProdTy [], L3.Ext $ L3.MemCpy dst src ty)]

isCursorArrayTy :: L3.Ty3 -> Bool
isCursorArrayTy L3.CursorArrayTy{} = True
isCursorArrayTy _ = False
