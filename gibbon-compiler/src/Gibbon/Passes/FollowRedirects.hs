module Gibbon.Passes.FollowRedirects
  ( followRedirects ) where


import Prelude hiding (tail)
import qualified Data.Map as M

import Gibbon.Common
import Gibbon.Language ( TyEnv, indirectionAlt, redirectionAlt, isPrinterName)
import Gibbon.L4.Syntax as L4

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

-- Track the tail that was returned with this tag var
type TagTailEnv = M.Map Var Var

followRedirects :: Prog -> PassM Prog
followRedirects (Prog info_tbl sym_tbl fundefs mainExp) = do
  fundefs' <- mapM followRedirectsFn fundefs
  mainExp' <- case mainExp of
                Just (PrintExp tail) ->
                  Just <$> PrintExp <$> followRedirectsExp False M.empty M.empty tail
                Nothing -> return Nothing
  return $ Prog info_tbl sym_tbl fundefs' mainExp'

followRedirectsFn :: FunDecl -> PassM FunDecl
followRedirectsFn f@FunDecl{funName,funArgs,funBody} = do
  let initTyEnv = M.fromList funArgs
      isPrintFn = isPrinterName funName
  bod' <- followRedirectsExp isPrintFn M.empty initTyEnv funBody
  return $ f {funBody = bod'}

followRedirectsExp :: Bool -> TagTailEnv -> TyEnv L4.Ty -> Tail -> PassM Tail
followRedirectsExp isPrintFn ttailenv tenv tail =
  case tail of
    Switch lbl trv alts bod_maybe -> do
      let trvty = typeOfTriv tenv trv
      case trvty of
        IntTy -> return $ Switch lbl trv alts bod_maybe
        -- OK, SymTy is Int64.
        SymTy -> return $ Switch lbl trv alts bod_maybe
        -- This is OK too - BoolTy is Int8.
        BoolTy -> return $ Switch lbl trv alts bod_maybe
        TagTyPacked -> do
          let VarTriv tagv = trv
              tailv = ttailenv # tagv
          vtmp <- gensym "tmpcur"
          ctmp <- gensym "tmpaftercur"
          tagtmp <- gensym "tagtmp"
          tailtmp <- gensym "tailtmp"
          let alttail = LetPrimCallT [(vtmp,CursorTy),(ctmp,CursorTy)] ReadTaggedCursor [VarTriv tailv] $
                          (LetPrimCallT [(tagtmp,TagTyPacked),(tailtmp,CursorTy)] ReadTag [VarTriv vtmp] $
                          (AssnValsT [(tagv , TagTyPacked, VarTriv tagtmp),
                                     (tailv, CursorTy   , VarTriv tailtmp)]
                          (Just (Goto lbl))))

              _alttail_ind = if isPrintFn
                            then LetPrimCallT [] (PrintString " ->i ") [] $ alttail
                            else alttail
              alttail_red = if isPrintFn
                            then LetPrimCallT [] (PrintString " ->r ") [] $ alttail
                            else alttail

          alts' <- case alts of
                    TagAlts ls -> do
                      ls' <- mapM (\(x,tl) -> (x,) <$> go tenv tl) ls
                      if indirectionAlt `elem` (map fst ls')
                      then return $ TagAlts $ ls' ++ [(redirectionAlt, alttail_red)]
                      else return $ TagAlts $ ls' ++ [(redirectionAlt, alttail_red)
                                                      -- (indirectionAlt, alttail_ind)
                                                     ]
                    IntAlts ls -> do
                      ls' <- mapM (\(x,tl) -> (x,) <$> go tenv tl) ls
                      if indirectionAlt `elem` (map fst ls')
                      then return $ IntAlts $ ls' ++ [(redirectionAlt, alttail_red)]
                      else return $ IntAlts $ ls' ++ [(redirectionAlt, alttail_red)
                                                      -- (indirectionAlt, alttail_ind)
                                                     ]
          return $ Switch lbl trv alts' bod_maybe
        _ -> error "followRedirectsExp: Shouldn't switch on any other type."

    Goto{} -> error "followRedirectsExp: Unexpected Goto."

    -- Straightforward recursion
    RetValsT{} -> return tail
    AssnValsT{} -> return tail
    LetCallT async binds rator rands bod ->
      LetCallT async binds rator rands <$>
        go (M.union tenv (M.fromList binds)) bod
    LetPrimCallT binds prim rands bod ->
      case binds of
        [(tag,TagTyPacked),(tail',CursorTy)] ->
          LetPrimCallT binds prim rands <$>
            followRedirectsExp isPrintFn (M.insert tag tail' ttailenv) (M.union tenv (M.fromList binds)) bod
        _ ->
          LetPrimCallT binds prim rands <$>
            go (M.union tenv (M.fromList binds)) bod
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
    LetAvailT vs bod -> do
      LetAvailT vs <$> go tenv bod
    IfT tst con els ->
      IfT tst <$> go tenv con <*> go tenv els
    ErrT{} -> return tail
    LetTimedT isIter binds timed bod ->
      LetTimedT isIter binds timed <$>
        go (M.union tenv (M.fromList binds)) bod
    LetArenaT lhs bod -> LetArenaT lhs <$> go (M.insert lhs ArenaTy tenv) bod
    TailCall{} -> return tail

  where go = followRedirectsExp isPrintFn ttailenv
