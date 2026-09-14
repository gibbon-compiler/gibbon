{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module SelectiveBufferSharing
  ( selectiveBufferSharingTests
  ) where

import Control.Exception (ErrorCall, evaluate, try)
import qualified Data.List as L
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3
import Gibbon.Passes.SelectiveBufferSharing


-- The cursorized calling convention these hand-built functions stand for.
-- Cursorize records it; a function without it has no convention to read, so
-- the passes under test decline rather than fall back to argument order.
abiTraversal :: Maybe [AbiRole]
abiTraversal = Just [AbiInEnd, AbiOutEnd, AbiOutCur, AbiInCur]

-- | The pass's own hard error requires --auto-loopification or
-- --opt-loopification to also be present -- selective buffer sharing only
-- ever rewrites functions loopification already rewrote. These tests
-- exercise SelectiveBufferSharing in isolation against a hand-built
-- already-loopified fixture (see 'loopifiedFun' etc.), so they set
-- Opt_AutoLoopification here purely to satisfy that precondition, exactly
-- as a real compile invoking both passes together always would.
runnerEnabled :: L3.Prog3 -> L3.Prog3
runnerEnabled prg =
  fst $
    runPassM
      (defaultConfig {dynflags = gopt_set Opt_AutoLoopification
                                    (gopt_set Opt_EnableSelectiveBufferSharing (dynflags defaultConfig))})
      0
      (selectiveBufferSharing prg)

runnerDisabled :: L3.Prog3 -> L3.Prog3
runnerDisabled prg =
  fst $ defaultPackedRunPassM $ selectiveBufferSharing prg

loopifiedProg :: L3.Prog3
loopifiedProg =
  Prog
    M.empty
    (M.fromList [("loopifiedMap", loopifiedFun)])
    Nothing

-- Note the cursorized SoA ABI (in_ends, out_ends, out_curs, in_curs).  The
-- pass only shares buffers of a function whose output cursor pair it can
-- identify: sharing installs a selective-indirection wrapper in the output, and
-- without the output pair no consumer call site would ever be normalized.
loopifiedFun :: L3.FunDef3
loopifiedFun =
  FunDef
    "loopifiedMap"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    (replicate 4 (L3.CursorArrayTy 3), L3.ProdTy [])
    loopifiedBody
    (FunMeta TailRec NoInline False [Loopified] abiTraversal)

loopifiedProducerFun :: L3.FunDef3
loopifiedProducerFun =
  FunDef
    "producer"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ( replicate 4 (L3.CursorArrayTy 3)
    , L3.ProdTy []
    )
    loopifiedBody
    (FunMeta TailRec NoInline False [Loopified] abiTraversal)

-- A fold over *two* packed SoA inputs.  After cursorization this has exactly
-- the same shape as a one-in/one-out map -- four equal-length cursor arrays --
-- but the pairs are (endsX, cursX) and (endsY, cursY), not (arg0, arg3).
consumer2Fun :: L3.FunDef3
consumer2Fun =
  FunDef
    "consumer2"
    ["endsX", "endsY", "cursX", "cursY"]
    (replicate 4 (L3.CursorArrayTy 3), L3.IntTy W64)
    (L3.mkLitE64 1)
    (FunMeta TailRec NoInline False [] Nothing)

twoInputCallSiteProg :: L3.Prog3
twoInputCallSiteProg =
  Prog
    M.empty
    (M.fromList [("producer", loopifiedProducerFun), ("consumer2", consumer2Fun)])
    (Just (twoInputCallSiteMain, L3.IntTy W64))

twoInputCallSiteMain :: L3.Exp3
twoInputCallSiteMain =
  L3.mkLets
    [ ("produce", [], L3.ProdTy [], L3.AppE "producer" UnknownTailType [] [L3.VarE "inEnds", L3.VarE "outEnds", L3.VarE "outCurs", L3.VarE "inCurs"])
    , ("consume", [], L3.IntTy W64, L3.AppE "consumer2" UnknownTailType [] [L3.VarE "outEnds", L3.VarE "inEnds", L3.VarE "outCurs", L3.VarE "inCurs"])
    ]
    (L3.VarE "consume")

-- A call whose argument is itself a call.  The rewriting walk rebuilds an
-- 'AppE' from its arguments without descending into them, so a consumer in
-- that position is never handed an unwrap.
nestedCallProg :: L3.Prog3
nestedCallProg =
  Prog
    M.empty
    (M.fromList
       [ ("producer", loopifiedProducerFun)
       , ("consumer", consumerFun)
       , ("identity", identityFun)
       ])
    (Just (nestedCallMain, L3.IntTy W64))

identityFun :: L3.FunDef3
identityFun =
  FunDef
    "identity"
    ["n"]
    ([L3.IntTy W64], L3.IntTy W64)
    (L3.VarE "n")
    (FunMeta NotRec NoInline False [] Nothing)

nestedCallMain :: L3.Exp3
nestedCallMain =
  L3.mkLets
    [ ("produce", [], L3.ProdTy [], L3.AppE "producer" UnknownTailType [] [L3.VarE "inEnds", L3.VarE "outEnds", L3.VarE "outCurs", L3.VarE "inCurs"])
    , ("consume", [], L3.IntTy W64
      , L3.AppE "identity" UnknownTailType []
          [L3.AppE "consumer" UnknownTailType [] [L3.VarE "outEnds", L3.VarE "outCurs"]])
    ]
    (L3.VarE "consume")

consumerFun :: L3.FunDef3
consumerFun =
  FunDef
    "consumer"
    ["ends", "curs"]
    ([L3.CursorArrayTy 3, L3.CursorArrayTy 3], L3.IntTy W64)
    (L3.mkLitE64 1)
    (FunMeta TailRec NoInline False [] Nothing)

callSiteProg :: L3.Prog3
callSiteProg =
  Prog
    M.empty
    (M.fromList [("producer", loopifiedProducerFun), ("consumer", consumerFun)])
    (Just (callSiteMain, L3.IntTy W64))

callSiteMain :: L3.Exp3
callSiteMain =
  -- This mimics the benchmark pipeline shape:
  -- a loopified map writes selective wrappers into its output SoA cursor
  -- arrays, and main passes a copied output start cursor array to a fold via
  -- an inline let-expression. The unwrap should be hoisted to that call site,
  -- not inserted inside the fold body where recursive calls would repeat it.
  L3.mkLets
    [ ("produce", [], L3.ProdTy [], L3.TimeIt (L3.AppE "producer" UnknownTailType [] [L3.VarE "inEnds", L3.VarE "outEnds", L3.VarE "outCurs", L3.VarE "inCurs"]) (L3.ProdTy []) False)
    , ("consume", [], L3.IntTy W64, L3.TimeIt (L3.AppE "consumer" UnknownTailType [] [L3.VarE "outEnds", inlineCopiedCursorArg "copyCurs" "outCurs"]) (L3.IntTy W64) False)
    ]
    (L3.VarE "consume")

inlineCopiedCursorArg :: Var -> Var -> L3.Exp3
inlineCopiedCursorArg dst src =
  L3.mkLets
    [ (dst, [], L3.CursorArrayTy 3, L3.Ext $ L3.InitCursor (L3.CursorArrayTy 3))
    , (toVar (fromVar dst ++ "_memcpy"), [], L3.ProdTy [], L3.Ext $ L3.MemCpy dst src (L3.CursorArrayTy 3))
    ]
    (L3.VarE dst)

loopifiedBody :: L3.Exp3
loopifiedBody =
  L3.mkLets
    (concatMap preludeFor [0, 1, 2] ++ [dconLoop, copyLoop, mutateLoop])
    (L3.MkProdE [])

preludeFor :: Int -> [(Var, [()], L3.Ty3, L3.Exp3)]
preludeFor = preludeForSeed "loop_probe"

preludeForSeed :: String -> Int -> [(Var, [()], L3.Ty3, L3.Exp3)]
preludeForSeed seed ix =
  let pfx = seed ++ "_buf" ++ show ix
   in [ (toVar (pfx ++ "_input_end"), [], L3.CursorTy, L3.Ext $ L3.IndexCursorArray "inEnds" ix)
      , (toVar (pfx ++ "_in_loc"), [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "inCurs" ix))
      , (toVar (pfx ++ "_out_loc"), [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outCurs" ix))
        -- Sharing writes the wrapper in one go and so needs somewhere to grow
        -- the output chunk; a buffer whose end loc it cannot see is declined.
      , (toVar (pfx ++ "_out_end_loc"), [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outEnds" ix))
      ]

dconLoop :: (Var, [()], L3.Ty3, L3.Exp3)
dconLoop =
  ( "loop_probe_buf0_loop"
  , []
  , L3.ProdTy []
  , L3.Ext $ L3.WhileCursor "loop_probe_buf0_count_footer_loc" $
      L3.mkLets
        [("loop_probe_buf0_inner_loop", [], L3.ProdTy [], L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) dconForBody)]
        (L3.MkProdE [])
  )

dconForBody :: L3.Exp3
dconForBody =
  L3.mkLets
    [("loop_probe_buf0_write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTagPacked "out_dcon" (L3.mkLitE64 1))]
    (L3.MkProdE [])

-- | A copy loop over buffer 1 of the named loop.
copyLoopSeed :: String -> (Var, [()], L3.Ty3, L3.Exp3)
copyLoopSeed seed =
  ( toVar (seed ++ "_buf1_loop")
  , []
  , L3.ProdTy []
  , L3.Ext $ L3.WhileCursor (toVar (seed ++ "_buf1_count_footer_loc")) $
      L3.mkLets
        [ ( toVar (seed ++ "_buf1_inner_loop"), [], L3.ProdTy []
          , L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) $
              L3.mkLets
                [ (toVar (seed ++ "_buf1_inner_body"), [], L3.ProdTy []
                  , copyScalarBodySeed seed 1) ]
                (L3.MkProdE []) ) ]
        (L3.MkProdE [])
  )

copyScalarBodySeed :: String -> Int -> L3.Exp3
copyScalarBodySeed seed ix =
  let pfx = seed ++ "_buf" ++ show ix
   in L3.mkLets
        [ (toVar (pfx ++ "_read_pair"), [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 (toVar (pfx ++ "_read_cur")))
        , (toVar (pfx ++ "_read_val"), [], L3.IntTy W64, L3.ProjE 0 (L3.VarE (toVar (pfx ++ "_read_pair"))))
        , (toVar (pfx ++ "_write_val"), [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 (toVar (pfx ++ "_write_cur")) (L3.VarE (toVar (pfx ++ "_read_val"))))
        ]
        (L3.MkProdE [])

-- | Two loops, from different loopifications, both copying their buffer 1.
--
-- Both preludes are learned before either loop is reached, so a per-buffer
-- environment keyed on the index alone has only the second loop's cursors by
-- then and would write both wrappers through them.
twoSeedProg :: L3.Prog3
twoSeedProg =
  Prog
    M.empty
    (M.fromList [("loopifiedMap", loopifiedFun { funBody = twoSeedBody })])
    Nothing

twoSeedBody :: L3.Exp3
twoSeedBody =
  L3.mkLets
    ( concatMap (preludeForSeed "loop_probe") [0, 1]
        ++ concatMap (preludeForSeed "loop_other") [0, 1]
        ++ [ dconLoopSeed "loop_probe", copyLoopSeed "loop_probe"
           , dconLoopSeed "loop_other", copyLoopSeed "loop_other" ] )
    (L3.MkProdE [])

-- | A tag-only loop over buffer 0 of the named loop.
dconLoopSeed :: String -> (Var, [()], L3.Ty3, L3.Exp3)
dconLoopSeed seed =
  ( toVar (seed ++ "_buf0_loop")
  , []
  , L3.ProdTy []
  , L3.Ext $ L3.WhileCursor (toVar (seed ++ "_buf0_count_footer_loc")) $
      L3.mkLets
        [ ( toVar (seed ++ "_buf0_inner_loop"), [], L3.ProdTy []
          , L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) $
              L3.mkLets
                [ ( toVar (seed ++ "_buf0_write_tag"), [], L3.CursorTy
                  , L3.Ext $ L3.WriteTagPacked "out_dcon" (L3.mkLitE64 1) ) ]
                (L3.MkProdE []) ) ]
        (L3.MkProdE [])
  )

copyLoop :: (Var, [()], L3.Ty3, L3.Exp3)
copyLoop =
  ( "loop_probe_buf1_loop"
  , []
  , L3.ProdTy []
  , L3.Ext $ L3.WhileCursor "loop_probe_buf1_count_footer_loc" $
      L3.mkLets
        [("loop_probe_buf1_inner_loop", [], L3.ProdTy [], L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) copyForBody)]
        (L3.MkProdE [])
  )

copyForBody :: L3.Exp3
copyForBody =
  L3.mkLets
    [("loop_probe_buf1_inner_body", [], L3.ProdTy [], copyScalarBody 1)]
    (L3.MkProdE [])

copyScalarBody :: Int -> L3.Exp3
copyScalarBody ix =
  let pfx = "loop_probe_buf" ++ show ix
   in L3.mkLets
        [ (toVar (pfx ++ "_read_pair"), [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 (toVar (pfx ++ "_read_cur")))
        , (toVar (pfx ++ "_read_val"), [], L3.IntTy W64, L3.ProjE 0 (L3.VarE (toVar (pfx ++ "_read_pair"))))
        , (toVar (pfx ++ "_write_val"), [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 (toVar (pfx ++ "_write_cur")) (L3.VarE (toVar (pfx ++ "_read_val"))))
        ]
        (L3.MkProdE [])

mutateLoop :: (Var, [()], L3.Ty3, L3.Exp3)
mutateLoop =
  ( "loop_probe_buf2_loop"
  , []
  , L3.ProdTy []
  , L3.Ext $ L3.WhileCursor "loop_probe_buf2_count_footer_loc" $
      L3.mkLets
        [("loop_probe_buf2_inner_loop", [], L3.ProdTy [], L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) mutateForBody)]
        (L3.MkProdE [])
  )

mutateForBody :: L3.Exp3
mutateForBody =
  L3.mkLets
    [("loop_probe_buf2_inner_body", [], L3.ProdTy [], mutateScalarBody)]
    (L3.MkProdE [])

crossFieldProg :: L3.Prog3
crossFieldProg =
  Prog
    M.empty
    (M.fromList [("loopifiedMap", loopifiedFun { funBody = crossFieldBody })])
    Nothing

crossFieldBody :: L3.Exp3
crossFieldBody =
  L3.mkLets
    (concatMap preludeFor [0, 1, 2] ++ [dconLoop, crossFieldLoop, mutateLoop])
    (L3.MkProdE [])

crossFieldLoop :: (Var, [()], L3.Ty3, L3.Exp3)
crossFieldLoop =
  ( "loop_probe_buf1_loop"
  , []
  , L3.ProdTy []
  , L3.Ext $ L3.WhileCursor "loop_probe_buf1_count_footer_loc" $
      L3.mkLets
        [("loop_probe_buf1_inner_loop", [], L3.ProdTy [], L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) crossFieldForBody)]
        (L3.MkProdE [])
  )

crossFieldForBody :: L3.Exp3
crossFieldForBody =
  L3.mkLets
    [("loop_probe_buf1_inner_body", [], L3.ProdTy [], crossFieldScalarBody)]
    (L3.MkProdE [])

-- Buffer 1 is written with a value read through its *cross-buffer dependency*
-- cursor on buffer 2, exactly as `LoopifyTraversals.mkDependencyRead` emits it.
-- Buffer 1 is therefore not a copy of itself and must not be shared.
crossFieldScalarBody :: L3.Exp3
crossFieldScalarBody =
  L3.mkLets
    [ ("loop_probe_buf1_read_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "loop_probe_buf1_read_cur")
    , ("loop_probe_buf1_read_val", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "loop_probe_buf1_read_pair"))
    , ("loop_probe_buf1_dep2_read_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "loop_probe_buf1_dep2_read_cur")
    , ("loop_probe_buf1_dep2_read_val", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "loop_probe_buf1_dep2_read_pair"))
    , ("loop_probe_buf1_field_val", [], L3.IntTy W64, L3.VarE "loop_probe_buf1_dep2_read_val")
    , ("loop_probe_buf1_write_val", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "loop_probe_buf1_write_cur" (L3.VarE "loop_probe_buf1_field_val"))
    ]
    (L3.MkProdE [])

mutateScalarBody :: L3.Exp3
mutateScalarBody =
  L3.mkLets
    [ ("loop_probe_buf2_read_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "loop_probe_buf2_read_cur")
    , ("loop_probe_buf2_read_val", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "loop_probe_buf2_read_pair"))
    , ("loop_probe_buf2_plus1", [], L3.IntTy W64, L3.PrimAppE addP64 [L3.VarE "loop_probe_buf2_read_val", L3.mkLitE64 1])
    , ("loop_probe_buf2_write_val", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "loop_probe_buf2_write_cur" (L3.VarE "loop_probe_buf2_plus1"))
    ]
    (L3.MkProdE [])

getFunBody :: Var -> L3.Prog3 -> L3.Exp3
getFunBody fn prg =
  case M.lookup fn (fundefs prg) of
    Just FunDef{funBody} -> funBody
    Nothing -> error $ "Missing function in test program: " ++ sdoc fn

countIndirections :: L3.Exp3 -> Int
countIndirections = countExt p
  where
    p L3.WriteCursorSelectiveIndirection{} = True
    p L3.WriteCursorIndirection{} = True
    p _ = False

countSelectiveUnwraps :: L3.Exp3 -> Int
countSelectiveUnwraps = countExt p
  where
    p L3.UnwrapSelectiveIndirections{} = True
    p _ = False

countTimedSelectiveUnwraps :: L3.Exp3 -> Int
countTimedSelectiveUnwraps ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> countTimedSelectiveUnwraps rhs + countTimedSelectiveUnwraps bod
    L3.IfE a b c -> sum (map countTimedSelectiveUnwraps [a, b, c])
    L3.CaseE scrt brs -> countTimedSelectiveUnwraps scrt + sum (map (countTimedSelectiveUnwraps . (\(_, _, rhs) -> rhs)) brs)
    L3.AppE _ _ _ args -> sum (map countTimedSelectiveUnwraps args)
    L3.PrimAppE _ args -> sum (map countTimedSelectiveUnwraps args)
    L3.MkProdE ls -> sum (map countTimedSelectiveUnwraps ls)
    L3.ProjE _ e -> countTimedSelectiveUnwraps e
    L3.DataConE _ _ args -> sum (map countTimedSelectiveUnwraps args)
    L3.TimeIt e _ _ -> countSelectiveUnwraps e + countTimedSelectiveUnwraps e
    L3.WithArenaE _ e -> countTimedSelectiveUnwraps e
    L3.SpawnE _ _ args -> sum (map countTimedSelectiveUnwraps args)
    L3.MapE (_, _, e1) e2 -> countTimedSelectiveUnwraps e1 + countTimedSelectiveUnwraps e2
    L3.FoldE (_, _, e1) (_, _, e2) e3 -> sum (map countTimedSelectiveUnwraps [e1, e2, e3])
    L3.Ext ext -> goExt ext
    _ -> 0
  where
    goExt ext =
      case ext of
        L3.ForE _ bound bod -> countTimedSelectiveUnwraps bound + countTimedSelectiveUnwraps bod
        L3.WhileCursor _ bod -> countTimedSelectiveUnwraps bod
        L3.WriteScalar _ _ rhs -> countTimedSelectiveUnwraps rhs
        L3.WriteTagPacked _ rhs -> countTimedSelectiveUnwraps rhs
        L3.WriteTaggedCursor _ rhs -> countTimedSelectiveUnwraps rhs
        L3.WriteCursorMutable _ rhs -> countTimedSelectiveUnwraps rhs
        L3.WriteList _ rhs _ -> countTimedSelectiveUnwraps rhs
        L3.WriteVector _ rhs _ -> countTimedSelectiveUnwraps rhs
        L3.AddCursor _ rhs -> countTimedSelectiveUnwraps rhs
        L3.BumpCursorMutable _ rhs -> countTimedSelectiveUnwraps rhs
        L3.AddrOfCursor rhs -> countTimedSelectiveUnwraps rhs
        L3.LetAvail _ bod -> countTimedSelectiveUnwraps bod
        L3.Assert rhs -> countTimedSelectiveUnwraps rhs
        _ -> 0

-- | Bounds checks sized for a selective-indirection wrapper.
countWrapperBoundsChecks :: L3.Exp3 -> Int
countWrapperBoundsChecks = countExt p
  where
    p (L3.BoundsCheck n _ _ _ _) = n == selectiveIndirectionSize
    p _ = False

countWhileCursors :: L3.Exp3 -> Int
countWhileCursors = countExt p
  where
    p L3.WhileCursor{} = True
    p _ = False

countExt :: (L3.E3Ext () L3.Ty3 -> Bool) -> L3.Exp3 -> Int
countExt p ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> countExt p rhs + countExt p bod
    L3.IfE a b c -> sum (map (countExt p) [a, b, c])
    L3.CaseE scrt brs -> countExt p scrt + sum (map (countExt p . (\(_, _, rhs) -> rhs)) brs)
    L3.AppE _ _ _ args -> sum (map (countExt p) args)
    L3.PrimAppE _ args -> sum (map (countExt p) args)
    L3.MkProdE ls -> sum (map (countExt p) ls)
    L3.ProjE _ e -> countExt p e
    L3.DataConE _ _ args -> sum (map (countExt p) args)
    L3.TimeIt e _ _ -> countExt p e
    L3.WithArenaE _ e -> countExt p e
    L3.SpawnE _ _ args -> sum (map (countExt p) args)
    L3.MapE (_, _, e1) e2 -> countExt p e1 + countExt p e2
    L3.FoldE (_, _, e1) (_, _, e2) e3 -> sum (map (countExt p) [e1, e2, e3])
    L3.Ext ext
      | p ext -> 1 + goExt ext
      | otherwise -> goExt ext
    _ -> 0
  where
    goExt ext =
      case ext of
        L3.ForE _ bound bod -> countExt p bound + countExt p bod
        L3.WhileCursor _ bod -> countExt p bod
        L3.WriteScalar _ _ rhs -> countExt p rhs
        L3.WriteTagPacked _ rhs -> countExt p rhs
        L3.WriteTaggedCursor _ rhs -> countExt p rhs
        L3.WriteCursorMutable _ rhs -> countExt p rhs
        L3.WriteList _ rhs _ -> countExt p rhs
        L3.WriteVector _ rhs _ -> countExt p rhs
        L3.AddCursor _ rhs -> countExt p rhs
        L3.BumpCursorMutable _ rhs -> countExt p rhs
        L3.AddrOfCursor rhs -> countExt p rhs
        L3.LetAvail _ bod -> countExt p bod
        L3.Assert rhs -> countExt p rhs
        _ -> 0

case_disabled_by_default :: Assertion
case_disabled_by_default =
  let body = getFunBody "loopifiedMap" (runnerDisabled loopifiedProg)
   in do
        0 @=? countIndirections body
        3 @=? countWhileCursors body

case_shares_dcon_and_copy_buffers :: Assertion
case_shares_dcon_and_copy_buffers =
  let body = getFunBody "loopifiedMap" (runnerEnabled loopifiedProg)
   in do
        2 @=? countIndirections body
        1 @=? countWhileCursors body

-- | The wrapper is written in one go at whatever cursor the replaced loop left
-- behind, so it needs its own room: the per-element growth the loop did is
-- gone with the loop.  One check per wrapper, sized to the wrapper.
-- | Two loops in one body must not answer for each other's buffers.
--
-- Buffer indices restart at zero in every loop, so a per-buffer environment
-- keyed on the index alone holds only the later loop's cursors by the time
-- either loop is rewritten, and both wrappers would be written through them --
-- into the wrong buffer for the earlier loop.  Each wrapper must dereference
-- its own loop's out loc.
case_two_loops_do_not_share_each_others_cursors :: Assertion
case_two_loops_do_not_share_each_others_cursors =
  let body = getFunBody "loopifiedMap" (runnerEnabled twoSeedProg)
      derefs = wrapperOutLocs body
   in do
        -- Two loops, each sharing its tag buffer and its copied buffer 1.
        4 @=? countIndirections body
        [ "loop_other_buf0_out_loc", "loop_other_buf1_out_loc"
          , "loop_probe_buf0_out_loc", "loop_probe_buf1_out_loc" ] @=? L.sort derefs

-- | The out loc each selective wrapper writes through, by name.
wrapperOutLocs :: L3.Exp3 -> [String]
wrapperOutLocs ex = go ex
  where
    go e =
      case e of
        L3.LetE (_, _, _, L3.Ext (L3.WriteCursorMutable loc _)) bod
          | "_out_loc" `L.isSuffixOf` fromVar loc -> fromVar loc : go bod
        L3.LetE (_, _, _, rhs) bod -> go rhs ++ go bod
        L3.IfE a b c -> go a ++ go b ++ go c
        L3.Ext (L3.WhileCursor _ bod) -> go bod
        L3.Ext (L3.ForE _ _ bod) -> go bod
        L3.TimeIt e' _ _ -> go e'
        _ -> []

case_each_shared_buffer_gets_room_for_its_wrapper :: Assertion
case_each_shared_buffer_gets_room_for_its_wrapper =
  let body = getFunBody "loopifiedMap" (runnerEnabled loopifiedProg)
   in do
        2 @=? countIndirections body
        2 @=? countWrapperBoundsChecks body

case_does_not_add_entry_unwrap_for_soa_input :: Assertion
case_does_not_add_entry_unwrap_for_soa_input =
  let prg = Prog M.empty (M.fromList [("consumer", consumerFun)]) Nothing
      body = getFunBody "consumer" (runnerEnabled prg)
   in 0 @=? countSelectiveUnwraps body

case_adds_call_site_unwrap_for_selective_output :: Assertion
case_adds_call_site_unwrap_for_selective_output =
  let prg = runnerEnabled callSiteProg
      body = getFunBody "consumer" prg
      mainUnwraps =
        case mainExp prg of
          Just (main, _) -> countSelectiveUnwraps main
          Nothing -> error "expected call-site test main expression"
      timedUnwraps =
        case mainExp prg of
          Just (main, _) -> countTimedSelectiveUnwraps main
          Nothing -> error "expected call-site test main expression"
   in do
        0 @=? countSelectiveUnwraps body
        1 @=? mainUnwraps
        0 @=? timedUnwraps

-- A buffer written from another buffer's dependency read is not a copy of
-- itself, so only the dcon stream may be shared and the cross-field loop must
-- survive.
case_does_not_share_cross_field_write :: Assertion
case_does_not_share_cross_field_write =
  let body = getFunBody "loopifiedMap" (runnerEnabled crossFieldProg)
   in do
        1 @=? countIndirections body
        2 @=? countWhileCursors body

-- A consumer taking two packed SoA inputs still gets its shared argument
-- normalized: the (ends, curs) pair is at argument positions 0 and 2, not the
-- 0/3 a one-in/one-out map would use.
case_adds_unwrap_for_two_input_consumer :: Assertion
case_adds_unwrap_for_two_input_consumer =
  let prg = runnerEnabled twoInputCallSiteProg
   in case mainExp prg of
        Just (main, _) -> 1 @=? countSelectiveUnwraps main
        Nothing -> error "expected two-input call-site test main expression"

-- A consumer of a shared value reached only through another call's argument
-- gets no unwrap: the walk rebuilds a call from its arguments without
-- descending into them.  The closed-world sweep must refuse it rather than let
-- the consumer read the 25-byte wrapper as data.
case_sweep_refuses_a_consumer_nested_in_a_call_argument :: Assertion
case_sweep_refuses_a_consumer_nested_in_a_call_argument = do
  r <- try (evaluate (length (show (runnerEnabled nestedCallProg))))
  case r :: Either ErrorCall Int of
    Right _ ->
      assertFailure
        "a marked (ends, curs) pair reaching a call with no unwrap must be refused"
    Left e ->
      assertBool ("unexpected error: " ++ show e)
        ("no UnwrapSelectiveIndirections" `L.isInfixOf` show e)

selectiveBufferSharingTests :: TestTree
selectiveBufferSharingTests = $(testGroupGenerator)
