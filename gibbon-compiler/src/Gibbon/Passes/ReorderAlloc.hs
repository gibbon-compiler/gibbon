module Gibbon.Passes.ReorderAlloc ( reorderAlloc ) where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.L3.Syntax

--------------------------------------------------------------------------------

reorderAlloc :: Prog3 -> PassM Prog3
reorderAlloc (Prog ddefs fundefs mainExp) = do
    fds' <- mapM gofun (M.elems fundefs)
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    mainExp' <- case mainExp of
                    Just (e,ty) -> do e' <- go e
                                      pure $ Just (e', ty)
                    Nothing     -> pure Nothing
    pure $ Prog ddefs fundefs' mainExp'

  where
    gofun f@FunDef{funBody} = do
        funBody' <- go funBody
        pure $ f { funBody = funBody' }

    go = reorderAllocExp

reorderAllocExp :: Exp3 -> PassM Exp3
reorderAllocExp = _todo
