-- | Fuse loopified scalar-buffer loops after selective buffer sharing.
--
-- `LoopifyTraversals` intentionally emits one chunk loop per scalar buffer.
-- That gives `SelectiveBufferSharing` a simple, local shape: any pure-copy
-- buffer can be replaced by one selective-indirection wrapper and its whole
-- loop can disappear.  This pass runs after selective sharing and fuses only
-- the remaining loopified scalar loops that still sit next to each other and
-- carry the same constructor label in their generated loop name.
--
-- The pass is conservative.  If the generated loop body no longer has the
-- expected chunk-loop shape, it leaves the loops alone.
module Gibbon.Passes.LoopifiedTraversalFusion
  ( fuseLoopifiedTraversals
  ) where

import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe (mapMaybe)

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3

type Bind3 = (Var, [()], L3.Ty3, L3.Exp3)

data ChunkLoop = ChunkLoop
  { clWhileCond :: Var
  , clPrefixBinds :: [Bind3]
  , clForVar :: Var
  , clForBound :: L3.Exp3
  , clForBody :: L3.Exp3
  , clBranchCond :: L3.Exp3
  , clThenBody :: L3.Exp3
  , clElseBody :: L3.Exp3
  }

fuseLoopifiedTraversals :: L3.Prog3 -> PassM L3.Prog3
fuseLoopifiedTraversals prog@Prog{fundefs} = do
  dflags <- getDynFlags
  let enabled = gopt Opt_EnableLoopFusion dflags
  fds' <-
    if enabled
    then mapM fuseFun (M.elems fundefs)
    else pure (M.elems fundefs)
  pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

fuseFun :: L3.FunDef3 -> PassM L3.FunDef3
fuseFun fn@FunDef{funMeta, funBody}
  | CanVectorize `notElem` funOpt funMeta = pure fn
  | otherwise = do
      body' <- fuseBody funBody
      pure $ fn { funBody = body' }

fuseBody :: L3.Exp3 -> PassM L3.Exp3
fuseBody ex = do
  let (binds, tailExp) = unLets3 ex
  binds' <- fuseBinds binds
  pure $ L3.mkLets binds' tailExp

fuseBinds :: [Bind3] -> PassM [Bind3]
fuseBinds [] = pure []
fuseBinds (b:bs) =
  case scalarLoopDCon b of
    Nothing -> (b :) <$> fuseBinds bs
    Just dconKey -> do
      let (grp, rest) = span ((== Just dconKey) . scalarLoopDCon) (b:bs)
      fusedOrOriginal <-
        if length grp < 2
        then pure grp
        else fuseGroup dconKey grp
      (fusedOrOriginal ++) <$> fuseBinds rest

fuseGroup :: String -> [Bind3] -> PassM [Bind3]
fuseGroup dconKey binds =
  case traverse parseChunkLoop binds of
    Nothing -> pure binds
    Just [] -> pure binds
    Just [_] -> pure binds
    Just loops@(rep:_) -> do
      fusedVar <- gensym $ toVar ("loopified_fused_" ++ dconKey)
      innerVar <- gensym $ toVar ("loopified_fused_" ++ dconKey ++ "_inner")
      branchVar <- gensym $ toVar ("loopified_fused_" ++ dconKey ++ "_branch")
      fusedForBody <- mkUnitSeq "loopified_fused_body" $
        [ substE (L3.VarE (clForVar loop)) (L3.VarE (clForVar rep)) (clForBody loop)
        | loop <- loops
        ]
      fusedThen <- mkUnitSeq "loopified_fused_then" (map clThenBody loops)
      fusedElse <- mkUnitSeq "loopified_fused_else" (map clElseBody loops)
      let fusedChunk =
            L3.mkLets
              ( concatMap clPrefixBinds loops
                ++ [ (innerVar, [], L3.ProdTy [], L3.Ext $ L3.ForE (clForVar rep) (clForBound rep) fusedForBody)
                   , (branchVar, [], L3.ProdTy [], L3.IfE (clBranchCond rep) fusedThen fusedElse)
                   ]
              )
              (L3.MkProdE [])
      pure [(fusedVar, [], L3.ProdTy [], L3.Ext $ L3.WhileCursor (clWhileCond rep) fusedChunk)]

mkUnitSeq :: String -> [L3.Exp3] -> PassM L3.Exp3
mkUnitSeq prefix bodies = do
  binds <-
    mapM
      (\body -> do
          v <- gensym (toVar prefix)
          pure (v, [], L3.ProdTy [], body))
      bodies
  pure $ L3.mkLets binds (L3.MkProdE [])

parseChunkLoop :: Bind3 -> Maybe ChunkLoop
parseChunkLoop (_, _, _, L3.Ext (L3.WhileCursor cond body)) = do
  let (binds, tailExp) = unLets3 body
  case tailExp of
    L3.MkProdE [] -> pure ()
    _ -> Nothing
  let (prefix, rest1) = break isForBind binds
  (forBind, rest2) <-
    case rest1 of
      x:xs -> Just (x, xs)
      [] -> Nothing
  (forVar, forBound, forBody) <- getFor forBind
  let (between, rest3) = break isIfBind rest2
  (branchBind, rest4) <-
    case rest3 of
      x:xs -> Just (x, xs)
      [] -> Nothing
  if null rest4
    then pure ()
    else Nothing
  (branchCond, thenBody, elseBody) <- getIf branchBind
  pure
    ChunkLoop
      { clWhileCond = cond
      , clPrefixBinds = prefix ++ between
      , clForVar = forVar
      , clForBound = forBound
      , clForBody = forBody
      , clBranchCond = branchCond
      , clThenBody = thenBody
      , clElseBody = elseBody
      }
parseChunkLoop _ = Nothing

isForBind :: Bind3 -> Bool
isForBind (_, _, _, L3.Ext L3.ForE{}) = True
isForBind _ = False

getFor :: Bind3 -> Maybe (Var, L3.Exp3, L3.Exp3)
getFor (_, _, _, L3.Ext (L3.ForE v bound body)) = Just (v, bound, body)
getFor _ = Nothing

isIfBind :: Bind3 -> Bool
isIfBind (_, _, _, L3.IfE{}) = True
isIfBind _ = False

getIf :: Bind3 -> Maybe (L3.Exp3, L3.Exp3, L3.Exp3)
getIf (_, _, _, L3.IfE cond thn els) = Just (cond, thn, els)
getIf _ = Nothing

scalarLoopDCon :: Bind3 -> Maybe String
scalarLoopDCon (v, _, _, L3.Ext L3.WhileCursor{}) =
  parseDConLoopName (fromVar v)
scalarLoopDCon _ = Nothing

parseDConLoopName :: String -> Maybe String
parseDConLoopName s = do
  rest <- firstJust [ L.stripPrefix "_dcon_" suffix | suffix <- L.tails s ]
  stripSuffix "_loop" rest

stripSuffix :: String -> String -> Maybe String
stripSuffix suffix s =
  let n = length suffix
   in if suffix `L.isSuffixOf` s
      then Just (take (length s - n) s)
      else Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust = safeHead . mapMaybe id
  where
    safeHead [] = Nothing
    safeHead (x:_) = Just x

unLets3 :: L3.Exp3 -> ([Bind3], L3.Exp3)
unLets3 ex =
  case ex of
    L3.LetE b bod ->
      let (bs, tailExp) = unLets3 bod
       in (b : bs, tailExp)
    _ -> ([], ex)
