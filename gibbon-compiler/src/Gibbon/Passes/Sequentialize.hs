{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Make sequential versions of parallel functions
module Gibbon.Passes.Sequentialize where

import           Data.Loc
import qualified Data.Map as M
import qualified Data.Set as S

import           Gibbon.Common
import           Gibbon.L1.Syntax
import           Gibbon.Passes.Flatten    (flattenL1)
import           Gibbon.Passes.InlineTriv (inlineTriv)

--------------------------------------------------------------------------------

sequentialize :: Prog1 -> PassM Prog1
sequentialize prg@Prog{fundefs}= do
  let parallel_fns = M.filter (\FunDef{funBody} -> hasParE funBody) fundefs
      parallel_fn_names = S.fromList $ M.keys parallel_fns
  seq_fns <- M.elems <$> mapM (sequentializeFn parallel_fn_names) parallel_fns
  let seq_fns_mp = M.fromList $ map (\f -> (funName f, f)) seq_fns
  let l1 = prg { fundefs = M.union fundefs seq_fns_mp }
  l1 <- flattenL1 l1
  l1 <- inlineTriv l1
  -- Running inlineTriv once doesn't eliminate variable aliasing. This
  -- is no good because InferLocations doesn't allow variable aliasing.
  -- So we run inlineTriv one more time to get rid of it.
  l1 <- inlineTriv l1
  pure l1

{-

Not implemented yet:

Keep taking things out of ParE if they're not big.

ParE a b c

big a && big b && big c -> ParE (a, b, c) + Nothing
big a && big b          -> ParE (a, b) + c
big a && big c          -> ParE (a, c) + b
big b && big c          -> ParE (b, c) + a
_                       -> ParE () + a + b + c

case (C_big a b c) could be a special case of how we check big.

-}

sequentializeFn :: S.Set Var -> FunDef1 -> PassM FunDef1
sequentializeFn parallel_fns fn@FunDef{funName,funBody} = do
  let new_fn_name = to_seq funName
  funBody' <- go funBody
  pure $ fn { funName = new_fn_name, funBody = funBody' }
  where
    to_seq v = varAppend v (toVar "_seq")

    go :: L Exp1 -> PassM (L Exp1)
    go (L p ex) = L p <$>
      case ex of
        VarE{} -> pure ex
        LitE{} -> pure ex
        LitSymE{} -> pure ex
        AppE f locs args | f `S.member` parallel_fns -> (AppE (to_seq f) locs) <$> (mapM go args)
                         | otherwise                 -> (AppE f locs) <$> (mapM go args)
        PrimAppE pr args -> (PrimAppE pr) <$> (mapM go args)
        LetE (v,locs,ty,L p1 (ParE ls)) bod -> do
          ws  <- mapM (\_ -> gensym "par_v_") ls
          ls' <- mapM go ls
          let rhs' = L p1 (MkProdE ls')
              n = length ls
              -- bod' = foldr
              --          (\(i,w) acc -> substE (l$ ProjE i (l$ VarE v)) (l$ VarE w) acc)
              --          bod
              --          (zip [0..(n-1)] ws)
          LetE (v,locs,ty,rhs') <$> go bod
        LetE (v,locs,ty,rhs) bod -> LetE <$> (v,locs,ty,) <$> go rhs <*> go bod
        IfE a b c  -> IfE <$> go a <*> go b <*> go c
        MkProdE ls -> MkProdE <$> mapM go ls
        ProjE i e  -> ProjE i <$> go e
        CaseE scrt brs -> CaseE <$> go scrt <*> mapM (\(a,b,c) -> (a,b,) <$> go c) brs
        DataConE loc dcon ls -> DataConE loc dcon <$> mapM go ls
        TimeIt e ty b -> do
          e' <- go e
          pure $ TimeIt e' ty b
        ParE ls -> pure $ MkProdE ls
        WithArenaE v e -> WithArenaE v <$> (go e)
        Ext{}   -> pure ex
        MapE{}  -> error "MapE"
        FoldE{} -> error "FoldE"
