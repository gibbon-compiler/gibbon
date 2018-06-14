{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Gibbon.Passes.RearrangeFree
  ( rearrangeFree ) where

import Gibbon.Common
import Gibbon.L4.Syntax

-- Ensure that any calls to `free` are the last thing in the program.
-- TODO: We should figure out a way to do this in Lower. Also `withTail`
-- _does_ end up duplicating some calls to `free`. Need to fix that.
rearrangeFree :: Prog -> PassM Prog
rearrangeFree (Prog fundefs mainExp) = do
  fundefs' <- mapM rearrangeFreeFn fundefs
  mainExp' <- case mainExp of
                Just (PrintExp tail) -> do
                  Just <$> PrintExp <$> rearrangeFreeExp Nothing tail
                Nothing -> return Nothing
  return $ Prog fundefs' mainExp'

rearrangeFreeFn :: FunDecl -> PassM FunDecl
rearrangeFreeFn f@FunDecl{funBody} = do
  bod' <- rearrangeFreeExp Nothing funBody
  return $ f {funBody = bod'}

rearrangeFreeExp :: Maybe (Tail -> Tail) -> Tail -> PassM Tail
rearrangeFreeExp frees tail =
  case tail of
    LetPrimCallT binds prim rands bod ->
      case prim of
        FreeBuffer -> do
            let clos = case frees of
                         Just f  -> f . LetPrimCallT binds prim rands
                         Nothing -> LetPrimCallT binds prim rands
            bod' <- rearrangeFreeExp (Just clos) bod
            return bod'
            -- withTail (bod', undefined) (\trvs -> clos (RetValsT trvs))
        _ -> LetPrimCallT binds prim rands <$> go bod

    -- RetValsT{} -> return tail
    RetValsT ls -> case frees of
                     Just f  -> return $ f (RetValsT ls)
                     Nothing -> return tail

    -- Straightforward recursion
    Switch lbl trv alts bod_maybe -> do
      alts' <- case alts of
                TagAlts ls -> do
                  ls' <- mapM (\(x,tl) -> (x,) <$> go tl) ls
                  return $ TagAlts ls'
                IntAlts ls -> do
                  ls' <- mapM (\(x,tl) -> (x,) <$> go tl) ls
                  return $ IntAlts ls'
      return $ Switch lbl trv alts' bod_maybe
    Goto{} -> return tail
    AssnValsT{} -> return tail
    LetCallT binds rator rands bod ->
      LetCallT binds rator rands <$>
        go bod
    LetTrivT bnd bod ->
      LetTrivT bnd <$> go bod
    LetIfT binds (trv,tl1,tl2) bod -> do
      tl1' <- go tl1
      tl2' <- go tl2
      LetIfT binds (trv, tl1', tl2') <$>
        go bod
    LetUnpackT binds ptr bod ->
      LetUnpackT binds ptr <$> go bod
    LetAllocT lhs vals bod -> do
      LetAllocT lhs vals <$> go bod
    IfT tst con els ->
      IfT tst <$> go con <*> go els
    ErrT{} -> return tail
    LetTimedT isIter binds timed bod ->
      LetTimedT isIter binds timed <$>
        go bod
    TailCall{} -> return tail

  where go = rearrangeFreeExp frees
