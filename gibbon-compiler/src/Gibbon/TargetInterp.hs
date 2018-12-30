-- | Interpreter for the target language (L4)

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Gibbon.TargetInterp
    ( Val(..), applyPrim
    , execProg
    ) where

--------------------------------------------------------------------------------

import Control.Monad
import qualified Data.Map.Strict as M
import Data.Maybe (listToMaybe)

import Data.Sequence (Seq, ViewL ((:<)), (|>))
import qualified Data.Sequence as Seq
import Gibbon.L4.Syntax
import Gibbon.Common (fromVar)
import GHC.Generics
import Control.DeepSeq
import Text.PrettyPrint.GenericPretty
import Text.PrettyPrint

-- import Data.Time.Clock
import System.Clock
--------------------------------------------------------------------------------

data Val
  = FunVal FunDecl
  | IntVal Int  -- ^ These also serve as Bools
  | TagVal Tag
  | BufVal (Seq Int)
      -- ^ Tags are also written as integers.
  deriving (Eq, Show, Generic, NFData)

instance NFData TimeSpec where
  rnf (TimeSpec !_ !_) = ()

{-
instance Out UTCTime where
    doc s = text (show s)
    docPrec n s = text (show s)
-}
instance Out TimeSpec where
    doc s = text (show s)
    docPrec _ s = text (show s)

instance Out Val

instance Out (Seq Int) where
    doc s = text (show s)
    docPrec _ s = text (show s)

execProg :: Prog -> IO [Val]
execProg (Prog _ Nothing) = error "Can't evaluate program: No expression given"
execProg (Prog funs (Just (PrintExp expr))) = exec env expr
  where
    env = M.fromList (map (\f -> (funName f, FunVal f)) funs)

type Env = M.Map Var Val


clk :: Clock
clk = Monotonic
-- Linux specific:
-- clk = MonotonicRaw


eval :: Env -> Triv -> Val
eval env (VarTriv v) = M.findWithDefault (error ("Unbound var: " ++ (fromVar v))) v env
eval _   (IntTriv i) = IntVal (fromIntegral i) -- TODO: Change L1 to Int64 too.
eval _   (TagTriv t) = TagVal t


exec :: Env -> Tail -> IO [Val]

exec env (RetValsT ts) = return $! map (eval env) ts

exec env (LetTrivT (v,_t,rhs) body) =
    exec env' body
  where
    env' = extendEnv env [(v,rhs')]
    rhs' = eval env rhs

exec env (LetCallT _async binds op args body) = do
    rets <- apply env (eval env (VarTriv op)) (map (eval env) args)
    let env' = extendEnv env (zip (map fst binds) rets)
    exec env' body

exec env (LetPrimCallT binds op args body) = do
    rets <- applyPrim op (map (eval env) args)
    let env' = extendEnv env (zip (map fst binds) rets)
    exec env' body

exec env (LetIfT bnds (tst,thn,els) bod) =
  do let scrut = eval env tst
     vals <- if scrut == IntVal 1
             then exec env thn
             else exec env els
     let env' = extendEnv env (zip (map fst bnds) vals)
     exec env' bod

exec env (IfT v1 then_ else_) =
    if v1' == IntVal 1 then exec env then_ else exec env else_
  where
    v1' = eval env v1

exec _ (ErrT s) =
    error $ "ErrT: " ++ s

exec env (LetTimedT flg bnds rhs bod) = do
    let iters = if flg then (error "Implement timed iteration inside the interpreter...")
                else 1
    !_ <- return $! force env
    st <- getTime clk
    vals <- foldM (\ _ i -> execWrapper i env rhs)
                  (error "Internal error: this should be unused.")
               [1..iters]
    en <- getTime clk
    let env' = extendEnv env (zip (map fst bnds) vals)
    let tm = fromIntegral (toNanoSecs $ diffTimeSpec en st)
              / 10e9 :: Double
    if flg
     then do putStrLn $ "ITERS: "++show iters
             putStrLn $ "SIZE: " ++show (error "FINISHME: get size param" :: Int)
             putStrLn $ "BATCHTIME: "++show tm
     else putStrLn $ "SELFTIMED: "++show tm
    exec env' bod

exec env (Switch _ tr alts def) =
    case final_alt of
      Nothing -> error "Switch: No branch to choose."
      Just br -> exec env br
  where
    tr' = eval env tr

    intAlts
      | IntAlts alts' <- alts
      = alts'
      | otherwise
      = error "intAlts: Found TagAlts"

    tagAlts
      | TagAlts alts' <- alts
      = alts'
      | otherwise
      = error "tagAlts: Found IntAlts"

    chooseIntAlt i = snd <$> listToMaybe (filter ((i ==) . fst) intAlts)
    chooseTagAlt t = snd <$> listToMaybe (filter ((t ==) . fst) tagAlts)

    final_alt =
      maybe def return $
        case tr' of
          IntVal i -> chooseIntAlt (fromIntegral i)
          TagVal t -> chooseTagAlt t
          _        -> error ("Switch: invalid value in scrutinee position: " ++ show tr')

exec env (TailCall fn args) =
    apply env fn' args'
  where
    fn' = eval env (VarTriv fn)
    args' = map (eval env) args

exec _ e = error$ "Interpreter/exec, unhandled expression:\n  "++show (doc e)

{-# NOINLINE execWrapper #-}
execWrapper :: Int -> Env -> Tail -> IO [Val]
execWrapper _i env ex = fmap force $ exec env ex

extendEnv :: Env -> [(Var, Val)] -> Env
extendEnv = foldr (uncurry M.insert)

apply :: Env -> Val -> [Val] -> IO [Val]

apply env (FunVal (FunDecl _ as _ body _)) args =
    exec (extendEnv env (zip (map fst as) args)) body

apply _ notFun _ =
    error ("apply to a non-function: " ++ show notFun)

--------------------------------------------------------------------------------

applyPrim :: Prim -> [Val] -> IO [Val]

applyPrim AddP [IntVal i1, IntVal i2] = pure [IntVal (i1 + i2)]
applyPrim SubP [IntVal i1, IntVal i2] = pure [IntVal (i1 - i2)]
applyPrim MulP [IntVal i1, IntVal i2] = pure [IntVal (i1 * i2)]

applyPrim EqP  [IntVal i1, IntVal i2] = pure [IntVal (if i1 == i2 then 1 else 0)]

applyPrim NewBuffer{} [] = pure [BufVal Seq.empty]

applyPrim WriteTag [TagVal tag, BufVal is] = pure [BufVal (is |> fromIntegral tag)]
applyPrim WriteInt [IntVal i,   BufVal is] = pure [BufVal (is |> i)]

applyPrim ReadTag [BufVal is] = case Seq.viewl is of
                                Seq.EmptyL -> error "ReadTag: Empty buffer"
                                t :< is'   -> pure [TagVal (fromIntegral t), BufVal is']

applyPrim ReadInt [BufVal is] = case Seq.viewl is of
                                Seq.EmptyL -> error "ReadInt: Empty buffer"
                                i :< is'   -> pure  [IntVal i, BufVal is']

applyPrim PrintInt [IntVal i] = do print i; return []
applyPrim (PrintString st) [] = do putStrLn st; return []

applyPrim SizeParam [] = error "TargetInterp/applyPrim: finish SizeParam"
applyPrim ScopedBuffer{} [] = error "TargetInterp/applyPrim: finish ScopedBuf"
applyPrim GetFirstWord [] = error "TargetInterp/applyPrim: finish GetFirstWord"

applyPrim (DictInsertP _) [] = error "TargetInterp/applyPrim: finish DictInsertP"
applyPrim (DictLookupP _) [] = error $ "TargetInterp/applyPrim: finish DictLookupP"
applyPrim (DictEmptyP _) []  = error $ "TargetInterp/applyPrim: finish DictEmptyP"


applyPrim op args = error ("applyPrim: Unsupported form or bad arguments: " ++ show op ++ " " ++ show args)
