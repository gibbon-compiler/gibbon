{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Packed.FirstOrder.Passes.FollowRedirects
  ( followRedirects ) where


import qualified Data.Map as M

import Packed.FirstOrder.Common hiding (FunDef(..))
import Packed.FirstOrder.L4.Syntax

{- [Modifying switch statements to use redirection nodes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If Gibbon is using "infinite" regions, it might insert redirections at the end
of regions. The current runtime representation of those is: (REDIRECTION_TAG PTR).
This redirection is added as another constructor to every data type. Thus,
every switch statement has to be modified to use this new constructor. We
achieve this with a combination of GOTO's and labels. Consider this example:

    {
        TagTyPacked tag = *cur;
        CursorTy tail = cur + 1;

        switch(tag) {
          case 0: ...
          case 1: ...
        }
        ...
    }

now becomes:

    {
        TagTyPacked tag = *cur;
        CursorTy tail = cur + 1;

        SWITCH_1: ;
        switch(tag) {
          case 0: ...
          case 1: ...

          case REDIRECTION:
            CursorTy redir = *(CursorTy *) tail;
            tag = *redir;
            tail = redir + 1;
            GOTO SWITCH_1;

        }
        ...
    }

-}

type TypeEnv = M.Map Var Ty

-- Track the tail that was returned with this tag var
type TagTailEnv = M.Map Var Var

followRedirects :: Prog -> SyM Prog
followRedirects (Prog fundefs mainExp) = do
  fundefs' <- mapM followRedirectsFn fundefs
  mainExp' <- case mainExp of
                Just (PrintExp tail) ->
                  Just <$> PrintExp <$> followRedirectsExp M.empty M.empty tail
                Nothing -> return Nothing
  return $ Prog fundefs' mainExp'

followRedirectsFn :: FunDecl -> SyM FunDecl
followRedirectsFn f@FunDecl{funArgs,funBody} = do
  let initTyEnv = M.fromList funArgs
  bod' <- followRedirectsExp M.empty initTyEnv funBody
  return $ f {funBody = bod'}

followRedirectsExp :: TagTailEnv -> TypeEnv -> Tail -> SyM Tail
followRedirectsExp ttailenv tenv tail =
  case tail of
    Switch lbl trv alts bod_maybe -> do
      let trvty = typeofTriv trv
      case trvty of
        IntTy -> return $ Switch lbl trv alts bod_maybe
        TagTyPacked -> do
          let VarTriv tagv = trv
              tailv = ttailenv # tagv
          vtmp <- gensym "tmpcur"
          ctmp <- gensym "tmpaftercur"
          tagtmp <- gensym "tagtmp"
          tailtmp <- gensym "tailtmp"
          let alttail = LetPrimCallT [(vtmp,CursorTy),(ctmp,CursorTy)] ReadCursor [VarTriv tailv] $
                          (LetPrimCallT [(tagtmp,TagTyPacked),(tailtmp,CursorTy)] ReadTag [VarTriv vtmp] $
                          (AssnValsT [(tagv , TagTyPacked, VarTriv tagtmp),
                                     (tailv, CursorTy   , VarTriv tailtmp)]
                          (Just (Goto lbl))))
          alts' <- case alts of
                    TagAlts ls -> do
                      ls' <- mapM (\(x,tl) -> (x,) <$> followRedirectsExp ttailenv tenv tl) ls
                      if indirectionAlt `elem` (map fst ls')
                      then return $ TagAlts $ ls' ++ [(redirectionAlt, alttail)]
                      else return $ TagAlts $ ls' ++ [(redirectionAlt, alttail),
                                                      (indirectionAlt, alttail)]
                    IntAlts ls -> do
                      ls' <- mapM (\(x,tl) -> (x,) <$> followRedirectsExp ttailenv tenv tl) ls
                      if indirectionAlt `elem` (map fst ls')
                      then return $ IntAlts $ ls' ++ [(redirectionAlt, alttail)]
                      else return $ IntAlts $ ls' ++ [(redirectionAlt, alttail),
                                                      (indirectionAlt, alttail)]
          return $ Switch lbl trv alts' bod_maybe
        _ -> error "followRedirectsExp: Shouldn't switch on any other type."

    Goto{} -> error "followRedirectsExp: Unexpected Goto."

    -- Straightforward recursion
    RetValsT{} -> return tail
    AssnValsT{} -> return tail
    LetCallT binds rator rands bod ->
      LetCallT binds rator rands <$>
        go (M.union tenv (M.fromList binds)) bod
    LetPrimCallT binds prim rands bod ->
      case binds of
        [(tag,TagTyPacked),(tail',CursorTy)] ->
          LetPrimCallT binds prim rands <$>
            followRedirectsExp (M.insert tag tail' ttailenv) (M.union tenv (M.fromList binds)) bod
        _ ->
          LetPrimCallT binds prim rands <$>
            followRedirectsExp ttailenv (M.union tenv (M.fromList binds)) bod
    LetTrivT bnd@(v,ty,_) bod ->
      LetTrivT bnd <$> go (M.insert v ty tenv) bod
    LetIfT binds (trv,tl1,tl2) bod -> do
      tl1' <- go tenv tl1
      tl2' <- go tenv tl2
      LetIfT binds (trv, tl1', tl2') <$>
        go (M.union tenv (M.fromList binds)) bod
    LetUnpackT binds ptr bod ->
      LetUnpackT binds ptr <$> go (M.union tenv (M.fromList binds)) bod
    LetAllocT lhs vals bod -> do
      LetAllocT lhs vals <$> go tenv bod
    IfT tst con els ->
      IfT tst <$> go tenv con <*> go tenv els
    ErrT{} -> return tail
    LetTimedT isIter binds timed bod ->
      LetTimedT isIter binds timed <$>
        go (M.union tenv (M.fromList binds)) bod
    TailCall{} -> return tail

  where go = followRedirectsExp ttailenv
        typeofTriv :: Triv -> Ty
        typeofTriv trv = case trv of
                           IntTriv{} -> IntTy
                           TagTriv{} -> TagTyPacked
                           VarTriv v -> tenv # v
