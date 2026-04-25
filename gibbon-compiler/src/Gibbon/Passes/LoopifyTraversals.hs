-- | Conservative loopification for a first class of `OPT:CanVectorize`
-- traversals.
--
-- The current rewrite only handles list-like fully-factored datatypes with:
-- - exactly one recursive constructor,
-- - exactly one nullary base constructor,
-- - exactly one recursive self field, and
-- - scalar field updates that are field-local.
--
-- The generated fast path is intentionally narrow:
-- - it only runs when scalar-count metadata is enabled,
-- - it only runs for single-chunk inputs,
-- - it checks that the current output chunks have enough room, and
-- - otherwise it falls back to the original recursive body unchanged.
--
-- This gets real loop-oriented IR into the pipeline without pretending that
-- multi-chunk chunk-walking is solved yet.
module Gibbon.Passes.LoopifyTraversals
  ( loopifyTraversals
  , LoopifyCandidate(..)
  , loopifyCandidateInfo
  , collectMentionedDataCons
  ) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import Gibbon.L3.Syntax

data LoopifyCandidate = LoopifyCandidate
  { lcFunName :: Var
  , lcTyCon :: TyCon
  , lcDataCons :: [DataCon]
  }
  deriving (Eq, Ord, Show)

data LinearLayoutInfo = LinearLayoutInfo
  { lliRecDCon :: DataCon
  , lliBaseDCon :: DataCon
  , lliScalarFieldTys :: [Ty3]
  }

data FieldPlan = FieldPlan
  { fpScalar :: Scalar
  , fpExpr :: Exp3
  }

loopifyTraversals :: Prog3 -> PassM Prog3
loopifyTraversals prog@Prog{ddefs, fundefs} = do
  dflags <- getDynFlags
  fds' <- mapM (rewriteFun ddefs) (M.elems fundefs)
             >>= \fs ->
                   if gopt Opt_StoreScalarFieldCounts dflags
                     then pure fs
                     else pure (M.elems fundefs)
  pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

rewriteFun :: DDefs Ty3 -> FunDef3 -> PassM FunDef3
rewriteFun ddefs fn =
  case loopifyCandidateInfo ddefs fn of
    Nothing -> pure fn
    Just cand ->
      case eligibleLinearLayout ddefs (lcTyCon cand) >>= \linfo ->
             loopifyFastPath ddefs linfo fn of
        Nothing -> pure fn
        Just body' -> pure $ fn { funBody = body' }

loopifyCandidateInfo :: DDefs Ty3 -> FunDef3 -> Maybe LoopifyCandidate
loopifyCandidateInfo ddefs FunDef{funName, funMeta, funBody}
  | CanVectorize `notElem` funOpt funMeta = Nothing
  | otherwise =
      let dcons = L.nub (collectMentionedDataCons funBody)
          tycons = L.nub (map (getTyOfDataCon ddefs) dcons)
       in case tycons of
            [tycon]
              | memLayout (lookupDDef ddefs tycon) == FullyFactored ->
                  Just LoopifyCandidate
                    { lcFunName = funName
                    , lcTyCon = tycon
                    , lcDataCons = dcons
                    }
            _ -> Nothing

eligibleLinearLayout :: DDefs Ty3 -> TyCon -> Maybe LinearLayoutInfo
eligibleLinearLayout ddefs tycon =
  let ddef = lookupDDef ddefs tycon
      isSelfPacked (_, PackedTy tc _) = tc == tycon
      isSelfPacked _ = False
      isScalarField (_, ty) = not (isPackedTy ty)
      recCtors =
        [ (dcon, scalarTys)
        | (dcon, fields) <- dataCons ddef
        , let recFields = filter isSelfPacked fields
        , length recFields == 1
        , null [ () | fld <- fields, isPackedTy (snd fld), not (isSelfPacked fld) ]
        , let scalarTys = map snd (filter isScalarField fields)
        ]
      baseCtors =
        [ dcon
        | (dcon, fields) <- dataCons ddef
        , null fields
        ]
   in case (recCtors, baseCtors) of
        ([(recDCon, scalarTys)], [baseDCon])
          | not (null scalarTys) ->
              Just LinearLayoutInfo
                { lliRecDCon = recDCon
                , lliBaseDCon = baseDCon
                , lliScalarFieldTys = scalarTys
                }
        _ -> Nothing

loopifyFastPath :: DDefs Ty3 -> LinearLayoutInfo -> FunDef3 -> Maybe Exp3
loopifyFastPath _ddefs LinearLayoutInfo{lliRecDCon, lliBaseDCon, lliScalarFieldTys} FunDef{funArgs, funTy = (ins, out), funBody}
  | otherwise =
      case (funArgs, ins) of
        ([inEnds, outEnds, outCurs, inCurs], [CursorArrayTy arr1, CursorArrayTy arr2, CursorArrayTy arr3, CursorArrayTy arr4])
          | arr1 == arr2
          , arr2 == arr3
          , arr3 == arr4
          , arr1 == 1 + length lliScalarFieldTys
          , out == loopifiedOutTy arr1 -> do
              plans <- extractFieldPlans lliRecDCon lliScalarFieldTys funBody
              pure $ mkFastPathBody arr1 inEnds outEnds outCurs inCurs lliRecDCon lliBaseDCon lliScalarFieldTys plans funBody
          | arr1 == arr2
          , arr2 == arr3
          , arr3 == arr4
          , arr1 == 1 + length lliScalarFieldTys
          , out == ProdTy [] -> do
              plans <- extractFieldPlans lliRecDCon lliScalarFieldTys funBody
              pure $ mkMutableFastPathBody inEnds outEnds outCurs inCurs lliRecDCon lliBaseDCon lliScalarFieldTys plans funBody
        _ -> Nothing

loopifiedOutTy :: Int -> Ty3
loopifiedOutTy arr =
  ProdTy
    [ CursorArrayTy arr
    , CursorArrayTy arr
    , CursorArrayTy arr
    , ProdTy [CursorArrayTy arr, CursorArrayTy arr]
    ]

mkFastPathBody :: Int -> Var -> Var -> Var -> Var -> DataCon -> DataCon -> [Ty3] -> [FieldPlan] -> Exp3 -> Exp3
mkFastPathBody arrLen inEnds outEnds outCurs inCurs _recDCon _baseDCon scalarTys plans fallbackBody =
  mkLets prelude $
    IfE (VarE fastOk) fastBody fallbackBody
  where
    scalarBufIndices = zip [1..] scalarTys
    firstScalarIx =
      case scalarBufIndices of
        (ix, _) : _ -> ix
        [] -> error "loopify: expected at least one scalar field"
    nm s = toVar ("loop_" ++ s)
    fieldNm s i = toVar ("loop_" ++ s ++ "_" ++ show i)

    inputEndScalar0 = nm "input_end_scalar0"
    firstFooter = nm "first_footer"
    nullFooter = nm "null_footer"
    isNullFooter = nm "is_null_footer"
    isEndFooter = nm "is_end_footer"
    singleChunk = nm "single_chunk"
    countVar = nm "chunk_count"
    dconOutLoc = nm "out_dcon_loc"
    dconInLoc = nm "in_dcon_loc"
    dconOutStart = nm "out_dcon_start"
    dconOutCur = nm "out_dcon_cur"
    dconOutEnd = nm "out_dcon_end"
    dconBytes = nm "dcon_bytes"
    dconReq = nm "dcon_req"
    dconFits = nm "dcon_fits"
    fastOk = nm "fast_ok"
    dconLoopIdx = nm "dcon_i"
    dconLoopRes = nm "dcon_loop_res"
    dconReadCur = nm "dcon_read_cur"
    dconReadPair = nm "dcon_read_pair"
    dconReadTag = nm "dcon_read_tag"
    dconWriteCur = nm "dcon_write_cur"
    dconWrite = nm "dcon_write"
    dconBump = nm "dcon_bump"
    dconInBump = nm "dcon_in_bump"
    dconBaseReadPair = nm "dcon_base_read_pair"
    dconBaseReadTag = nm "dcon_base_read_tag"
    dconBaseReadCur = nm "dcon_base_read_cur"
    dconBaseCur = nm "dcon_base_cur"
    dconBaseWrite = nm "dcon_base_write"
    dconBaseBump = nm "dcon_base_bump"
    dconBaseInBump = nm "dcon_base_in_bump"
    overwriteReg = nm "overwrite_reg"
    inDconCur = nm "in_dcon_cur"
    inDconEnd = nm "in_dcon_end"
    outFinalCur = nm "out_final_cur"
    inFinalArr = nm "in_final_arr"
    outFinalArr = nm "out_final_arr"
    packedPair = nm "packed_pair"

    prelude =
      [ (inputEndScalar0, [], CursorTy, indexCursorExp inEnds firstScalarIx)
      , (firstFooter, [], CursorTy, Ext $ ReadScalarCountFirstFooter inputEndScalar0)
      , (nullFooter, [], CursorTy, Ext NullCursor)
      , (isNullFooter, [], BoolTy, PrimAppE EqIntP [VarE firstFooter, VarE nullFooter])
      , (isEndFooter, [], BoolTy, PrimAppE EqIntP [VarE firstFooter, VarE inputEndScalar0])
      , (singleChunk, [], BoolTy, PrimAppE OrP [VarE isNullFooter, VarE isEndFooter])
      , (countVar, [], IntTy, Ext $ ReadScalarCount inputEndScalar0)
      , (dconOutStart, [], CursorTy, indexCursorExp outCurs 0)
      , (dconOutLoc, [], MutCursorTy, Ext $ AddrOfCursor (VarE dconOutStart))
      , (dconOutCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
      , (dconOutEnd, [], CursorTy, indexCursorExp outEnds 0)
      , (dconBytes, [], IntTy, PrimAppE AddP [VarE countVar, LitE 1])
      , (dconReq, [], CursorTy, Ext $ AddCursor dconOutCur (VarE dconBytes))
      , (dconFits, [], BoolTy, PrimAppE LtEqP [VarE dconReq, VarE dconOutEnd])
      , (inDconCur, [], CursorTy, indexCursorExp inCurs 0)
      , (dconInLoc, [], MutCursorTy, Ext $ AddrOfCursor (VarE inDconCur))
      ]
      ++ concatMap mkFieldPrelude (zip3 scalarBufIndices plans [0 :: Int ..])
      ++ [ (overwriteReg, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (dconOutEnd : map fieldOutEndVar [0 :: Int .. length plans - 1]))
         , (fastOk, [], BoolTy, mkAllAnd (VarE singleChunk : VarE dconFits : map (VarE . fieldFitsVar) [0 :: Int .. length plans - 1]))
         ]

    mkFieldPrelude (((bufIx, ty), FieldPlan{}, planIx)) =
      let inStart = fieldInStartVar planIx
          outStart = fieldOutStartVar planIx
          inLoc = fieldInLocVar planIx
          outLoc = fieldOutLocVar planIx
          outCur = fieldOutCurVar planIx
          outEnd = fieldOutEndVar planIx
          reqBytes = fieldReqBytesVar planIx
          reqEnd = fieldReqEndVar planIx
          fits = fieldFitsVar planIx
          scalarBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc ty) (sizeOfTy ty)
       in [ (inStart, [], CursorTy, indexCursorExp inCurs bufIx)
          , (outStart, [], CursorTy, indexCursorExp outCurs bufIx)
          , (inLoc, [], MutCursorTy, Ext $ AddrOfCursor (VarE inStart))
          , (outLoc, [], MutCursorTy, Ext $ AddrOfCursor (VarE outStart))
          , (outCur, [], CursorTy, Ext $ DerefMutCursor outLoc)
          , (outEnd, [], CursorTy, indexCursorExp outEnds bufIx)
          , (reqBytes, [], IntTy, PrimAppE MulP [VarE countVar, LitE scalarBytes])
          , (reqEnd, [], CursorTy, Ext $ AddCursor outCur (VarE reqBytes))
          , (fits, [], BoolTy, PrimAppE LtEqP [VarE reqEnd, VarE outEnd])
          ]

    fastBody =
      mkLets
        ( [ (dconLoopRes, [], ProdTy [], Ext $ ForE dconLoopIdx (VarE countVar) dconLoopBody) ]
          ++ writeBaseTag
          ++ concatMap mkFieldLoop (zip3 scalarBufIndices plans [0 :: Int ..])
          ++ [ (outFinalCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
             , (inDconEnd, [], CursorTy, Ext $ DerefMutCursor dconInLoc)
             ]
          ++ concatMap mkFieldFinalLets [0 :: Int .. length plans - 1]
          ++ [ (inFinalArr, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (inDconEnd : map fieldFinalInVar [0 :: Int .. length plans - 1]))
             , (outFinalArr, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (outFinalCur : map fieldFinalOutVar [0 :: Int .. length plans - 1]))
             , (packedPair, [], ProdTy [CursorArrayTy arrLen, CursorArrayTy arrLen], MkProdE [VarE outCurs, VarE outFinalArr])
             ]
        )
        (MkProdE [VarE inEnds, VarE overwriteReg, VarE inFinalArr, VarE packedPair])

    dconLoopBody =
      mkLets
        [ (dconReadCur, [], CursorTy, Ext $ DerefMutCursor dconInLoc)
        , (dconReadPair, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag dconReadCur)
        , (dconReadTag, [], IntTy, ProjE 0 (VarE dconReadPair))
        , (dconWriteCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
        , (dconWrite, [], CursorTy, Ext $ WriteTagPacked dconWriteCur (VarE dconReadTag))
        , (dconBump, [], ProdTy [], Ext $ BumpCursorMutable dconOutLoc (LitE 1))
        , (dconInBump, [], ProdTy [], Ext $ BumpCursorMutable dconInLoc (LitE 1))
        ]
        (MkProdE [])

    writeBaseTag =
      [ (dconBaseReadCur, [], CursorTy, Ext $ DerefMutCursor dconInLoc)
      , (dconBaseReadPair, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag dconBaseReadCur)
      , (dconBaseReadTag, [], IntTy, ProjE 0 (VarE dconBaseReadPair))
      , (dconBaseCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
      , (dconBaseWrite, [], CursorTy, Ext $ WriteTagPacked dconBaseCur (VarE dconBaseReadTag))
      , (dconBaseBump, [], ProdTy [], Ext $ BumpCursorMutable dconOutLoc (LitE 1))
      , (dconBaseInBump, [], ProdTy [], Ext $ BumpCursorMutable dconInLoc (LitE 1))
      ]

    mkFieldLoop (((_bufIx, ty), FieldPlan{fpScalar, fpExpr}, planIx)) =
      let loopIdx = fieldNm "field_i" planIx
          inCur = fieldNm "in_cur" planIx
          readPair = fieldNm "read_pair" planIx
          readVal = fieldNm "read_val" planIx
          fieldVal = fieldNm "field_val" planIx
          outCur = fieldNm "out_cur" planIx
          writeCur = fieldNm "write_cur" planIx
          bumpIn = fieldNm "bump_in" planIx
          bumpOut = fieldNm "bump_out" planIx
          loopRes = fieldNm "body" planIx
          scalarBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc ty) (sizeOfTy ty)
          loopBody =
            mkLets
              [ (inCur, [], CursorTy, Ext $ DerefMutCursor (fieldInLocVar planIx))
              , (readPair, [], ProdTy [ty, CursorTy], Ext $ ReadScalar fpScalar inCur)
              , (readVal, [], ty, ProjE 0 (VarE readPair))
              , (fieldVal, [], ty, substFieldValue fpExpr readVal)
              , (outCur, [], CursorTy, Ext $ DerefMutCursor (fieldOutLocVar planIx))
              , (writeCur, [], CursorTy, Ext $ WriteScalar fpScalar outCur (VarE fieldVal))
              , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (fieldInLocVar planIx) (LitE scalarBytes))
              , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (fieldOutLocVar planIx) (LitE scalarBytes))
              ]
              (MkProdE [])
       in [ (loopRes, [], ProdTy [], Ext $ ForE loopIdx (VarE countVar) loopBody) ]

    fieldInLocVar i = fieldNm "in_loc" i
    fieldInStartVar i = fieldNm "in_start" i
    fieldOutLocVar i = fieldNm "out_loc" i
    fieldOutStartVar i = fieldNm "out_start" i
    fieldOutCurVar i = fieldNm "out_cur_pre" i
    fieldOutEndVar i = fieldNm "out_end" i
    fieldReqBytesVar i = fieldNm "req_bytes" i
    fieldReqEndVar i = fieldNm "req_end" i
    fieldFitsVar i = fieldNm "fits" i
    fieldFinalInVar i = fieldNm "in_final" i
    fieldFinalOutVar i = fieldNm "out_final" i
    mkFieldFinalLets i =
      [ (fieldFinalInVar i, [], CursorTy, Ext $ DerefMutCursor (fieldInLocVar i))
      , (fieldFinalOutVar i, [], CursorTy, Ext $ DerefMutCursor (fieldOutLocVar i))
      ]

    indexCursorExp arr ix = Ext $ IndexCursorArray arr ix

    mkAllAnd :: [Exp3] -> Exp3
    mkAllAnd [] = PrimAppE MkTrue []
    mkAllAnd [e] = e
    mkAllAnd (e:es) = PrimAppE AndP [e, mkAllAnd es]

    substFieldValue :: Exp3 -> Var -> Exp3
    substFieldValue ex newV =
      case S.toList (gFreeVars ex) of
        [] -> ex
        [v] -> substE (VarE v) (VarE newV) ex
        _ -> ex

mkMutableFastPathBody :: Var -> Var -> Var -> Var -> DataCon -> DataCon -> [Ty3] -> [FieldPlan] -> Exp3 -> Exp3
mkMutableFastPathBody inEnds outEnds outCurs inCurs _recDCon _baseDCon scalarTys plans fallbackBody =
  mkLets prelude $
    IfE (VarE fastOk) fastBody fallbackBody
  where
    scalarBufIndices = zip [1..] scalarTys
    firstScalarIx =
      case scalarBufIndices of
        (ix, _) : _ -> ix
        [] -> error "loopify: expected at least one scalar field"
    nm s = toVar ("loop_mut_" ++ s)
    fieldNm s i = toVar ("loop_mut_" ++ s ++ "_" ++ show i)

    inputEndScalar0 = nm "input_end_scalar0"
    firstFooter = nm "first_footer"
    nullFooter = nm "null_footer"
    countFooterCur = nm "count_footer_cur"
    countFooterLoc = nm "count_footer_loc"
    nextFooterCur = nm "next_footer_cur"
    nextFooterLoc = nm "next_footer_loc"
    firstCount = nm "first_chunk_count"
    dconInLoc = nm "in_dcon_loc"
    dconOutLoc = nm "out_dcon_loc"
    dconOutEndLoc = nm "out_dcon_end_loc"
    dconOutCur = nm "out_dcon_cur"
    dconOutEnd = nm "out_dcon_end"
    dconBytes = nm "dcon_bytes"
    dconReq = nm "dcon_req"
    dconFits = nm "dcon_fits"
    fastOk = nm "fast_ok"
    chunkLoop = nm "chunk_loop"
    currentCountFooter = nm "current_count_footer"
    chunkCount = nm "chunk_count"
    currentNextFooter = nm "current_next_footer"
    isNullNextFooter = nm "is_null_next_footer"
    isEndNextFooter = nm "is_end_next_footer"
    isLastChunk = nm "is_last_chunk"
    dconLoopIdx = nm "dcon_i"
    dconLoopRes = nm "dcon_loop_res"
    dconReadCur = nm "dcon_read_cur"
    dconReadPair = nm "dcon_read_pair"
    dconReadTag = nm "dcon_read_tag"
    dconWriteCur = nm "dcon_write_cur"
    dconWrite = nm "dcon_write"
    dconOutBump = nm "dcon_out_bump"
    dconInBump = nm "dcon_in_bump"
    boundaryReadCur = nm "boundary_read_cur"
    boundaryPair = nm "boundary_pair"
    boundaryTag = nm "boundary_tag"
    boundaryAfter = nm "boundary_after"
    chunkBranch = nm "chunk_branch"
    dconBaseCur = nm "dcon_base_cur"
    dconBaseWrite = nm "dcon_base_write"
    dconBaseOutBump = nm "dcon_base_out_bump"
    dconBaseSetIn = nm "dcon_base_set_in"
    dconRedirPair = nm "dcon_redir_pair"
    dconNextStart = nm "dcon_next_start"
    dconGrow = nm "dcon_grow"
    dconSetIn = nm "dcon_set_in"
    nextNextFooter = nm "next_next_footer"
    updateCountFooter = nm "update_count_footer"
    updateNextFooter = nm "update_next_footer"

    prelude =
      [ (inputEndScalar0, [], CursorTy, indexCursorExp inEnds firstScalarIx)
      , (firstFooter, [], CursorTy, Ext $ ReadScalarCountFirstFooter inputEndScalar0)
      , (nullFooter, [], CursorTy, Ext NullCursor)
      , (countFooterCur, [], CursorTy, VarE inputEndScalar0)
      , (countFooterLoc, [], MutCursorTy, Ext $ AddrOfCursor (VarE countFooterCur))
      , (nextFooterCur, [], CursorTy, VarE firstFooter)
      , (nextFooterLoc, [], MutCursorTy, Ext $ AddrOfCursor (VarE nextFooterCur))
      , (firstCount, [], IntTy, Ext $ ReadScalarCount inputEndScalar0)
      , (dconInLoc, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp inCurs 0))
      , (dconOutLoc, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outCurs 0))
      , (dconOutEndLoc, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outEnds 0))
      , (dconOutCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
      , (dconOutEnd, [], CursorTy, indexCursorExp outEnds 0)
      , (dconBytes, [], IntTy, PrimAppE AddP [VarE firstCount, LitE 9])
      , (dconReq, [], CursorTy, Ext $ AddCursor dconOutCur (VarE dconBytes))
      , (dconFits, [], BoolTy, PrimAppE LtEqP [VarE dconReq, VarE dconOutEnd])
      ]
      ++ concatMap mkFieldPrelude (zip3 scalarBufIndices plans [0 :: Int ..])
      ++
      [ (fastOk, [], BoolTy, mkAllAnd (VarE dconFits : map (VarE . fieldFitsVar) [0 :: Int .. length plans - 1]))
      ]

    mkFieldPrelude (((bufIx, ty), FieldPlan{}, planIx)) =
      let inLoc = fieldInLocVar planIx
          outLoc = fieldOutLocVar planIx
          outEndLoc = fieldOutEndLocVar planIx
          outCur = fieldOutCurVar planIx
          outEnd = fieldOutEndVar planIx
          reqBytes = fieldReqBytesVar planIx
          reqEnd = fieldReqEndVar planIx
          fits = fieldFitsVar planIx
          scalarBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc ty) (sizeOfTy ty)
       in [ (inLoc, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp inCurs bufIx))
          , (outLoc, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outCurs bufIx))
          , (outEndLoc, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outEnds bufIx))
          , (outCur, [], CursorTy, Ext $ DerefMutCursor outLoc)
          , (outEnd, [], CursorTy, indexCursorExp outEnds bufIx)
          , (reqBytes, [], IntTy, PrimAppE MulP [VarE firstCount, LitE scalarBytes])
          , (reqEnd, [], CursorTy, Ext $ AddCursor outCur (VarE reqBytes))
          , (fits, [], BoolTy, PrimAppE LtEqP [VarE reqEnd, VarE outEnd])
          ]

    fastBody =
      mkLets
        [ (chunkLoop, [], ProdTy [], Ext $ WhileCursor countFooterLoc chunkLoopBody) ]
        (MkProdE [])

    chunkLoopBody =
      mkLets
        ( [ (currentCountFooter, [], CursorTy, Ext $ DerefMutCursor countFooterLoc)
          , (chunkCount, [], IntTy, Ext $ ReadScalarCount currentCountFooter)
          , (currentNextFooter, [], CursorTy, Ext $ DerefMutCursor nextFooterLoc)
          , (isNullNextFooter, [], BoolTy, PrimAppE EqIntP [VarE currentNextFooter, VarE nullFooter])
          , (isEndNextFooter, [], BoolTy, PrimAppE EqIntP [VarE currentNextFooter, VarE inputEndScalar0])
          , (isLastChunk, [], BoolTy, PrimAppE OrP [VarE isNullNextFooter, VarE isEndNextFooter])
          , (dconLoopRes, [], ProdTy [], Ext $ ForE dconLoopIdx (VarE chunkCount) dconLoopBody)
          ]
          ++ concatMap mkFieldLoop (zip3 scalarBufIndices plans [0 :: Int ..])
          ++ [ (boundaryReadCur, [], CursorTy, Ext $ DerefMutCursor dconInLoc)
             , (boundaryPair, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag boundaryReadCur)
             , (boundaryTag, [], IntTy, ProjE 0 (VarE boundaryPair))
             , (boundaryAfter, [], CursorTy, ProjE 1 (VarE boundaryPair))
             , (chunkBranch, [], ProdTy [], IfE (VarE isLastChunk) lastChunkBody continueChunkBody)
             ]
        )
        (MkProdE [])

    dconLoopBody =
      mkLets
        [ (dconReadCur, [], CursorTy, Ext $ DerefMutCursor dconInLoc)
        , (dconReadPair, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag dconReadCur)
        , (dconReadTag, [], IntTy, ProjE 0 (VarE dconReadPair))
        , (dconWriteCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
        , (dconWrite, [], CursorTy, Ext $ WriteTagPacked dconWriteCur (VarE dconReadTag))
        , (dconOutBump, [], ProdTy [], Ext $ BumpCursorMutable dconOutLoc (LitE 1))
        , (dconInBump, [], ProdTy [], Ext $ BumpCursorMutable dconInLoc (LitE 1))
        ]
        (MkProdE [])

    lastChunkBody =
      mkLets
        [ (dconBaseCur, [], CursorTy, Ext $ DerefMutCursor dconOutLoc)
        , (dconBaseWrite, [], CursorTy, Ext $ WriteTagPacked dconBaseCur (VarE boundaryTag))
        , (dconBaseOutBump, [], ProdTy [], Ext $ BumpCursorMutable dconOutLoc (LitE 1))
        , (dconBaseSetIn, [], ProdTy [], Ext $ WriteCursorMutable dconInLoc (VarE boundaryAfter))
        , (updateCountFooter, [], ProdTy [], Ext $ WriteCursorMutable countFooterLoc (VarE nullFooter))
        ]
        (MkProdE [])

    continueChunkBody =
      mkLets
        ( [ (dconRedirPair, [], ProdTy [CursorTy, CursorTy, IntTy], Ext $ ReadTaggedCursor boundaryAfter)
          , (dconNextStart, [], CursorTy, ProjE 0 (VarE dconRedirPair))
          , (dconGrow, [], ProdTy [], Ext $ GrowRegion dconOutLoc dconOutEndLoc)
          , (dconSetIn, [], ProdTy [], Ext $ WriteCursorMutable dconInLoc (VarE dconNextStart))
          ]
          ++ concatMap mkFieldContinue [0 :: Int .. length plans - 1]
          ++ [ (nextNextFooter, [], CursorTy, Ext $ ReadScalarCountNextFooter currentNextFooter)
             , (updateCountFooter, [], ProdTy [], Ext $ WriteCursorMutable countFooterLoc (VarE currentNextFooter))
             , (updateNextFooter, [], ProdTy [], Ext $ WriteCursorMutable nextFooterLoc (VarE nextNextFooter))
             ]
        )
        (MkProdE [])

    mkFieldLoop (((_bufIx, ty), FieldPlan{fpScalar, fpExpr}, planIx)) =
      let loopIdx = fieldNm "field_i" planIx
          inCur = fieldNm "in_cur" planIx
          readPair = fieldNm "read_pair" planIx
          readVal = fieldNm "read_val" planIx
          fieldVal = fieldNm "field_val" planIx
          outCur = fieldNm "out_cur" planIx
          writeCur = fieldNm "write_cur" planIx
          bumpIn = fieldNm "bump_in" planIx
          bumpOut = fieldNm "bump_out" planIx
          loopRes = fieldNm "body" planIx
          scalarBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc ty) (sizeOfTy ty)
          loopBody =
            mkLets
              [ (inCur, [], CursorTy, Ext $ DerefMutCursor (fieldInLocVar planIx))
              , (readPair, [], ProdTy [ty, CursorTy], Ext $ ReadScalar fpScalar inCur)
              , (readVal, [], ty, ProjE 0 (VarE readPair))
              , (fieldVal, [], ty, substFieldValue fpExpr readVal)
              , (outCur, [], CursorTy, Ext $ DerefMutCursor (fieldOutLocVar planIx))
              , (writeCur, [], CursorTy, Ext $ WriteScalar fpScalar outCur (VarE fieldVal))
              , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (fieldInLocVar planIx) (LitE scalarBytes))
              , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (fieldOutLocVar planIx) (LitE scalarBytes))
              ]
              (MkProdE [])
       in [ (loopRes, [], ProdTy [], Ext $ ForE loopIdx (VarE chunkCount) loopBody) ]

    mkFieldContinue planIx =
      let boundaryCur = fieldNm "boundary_cur" planIx
          boundaryPair' = fieldNm "boundary_pair" planIx
          boundaryAfter' = fieldNm "boundary_after" planIx
          redirPair = fieldNm "redir_pair" planIx
          nextStart = fieldNm "next_start" planIx
          growOut = fieldNm "grow_out" planIx
          setIn = fieldNm "set_in" planIx
       in [ (boundaryCur, [], CursorTy, Ext $ DerefMutCursor (fieldInLocVar planIx))
          , (boundaryPair', [], ProdTy [IntTy, CursorTy], Ext $ ReadTag boundaryCur)
          , (boundaryAfter', [], CursorTy, ProjE 1 (VarE boundaryPair'))
          , (redirPair, [], ProdTy [CursorTy, CursorTy, IntTy], Ext $ ReadTaggedCursor boundaryAfter')
          , (nextStart, [], CursorTy, ProjE 0 (VarE redirPair))
          , (growOut, [], ProdTy [], Ext $ GrowRegion (fieldOutLocVar planIx) (fieldOutEndLocVar planIx))
          , (setIn, [], ProdTy [], Ext $ WriteCursorMutable (fieldInLocVar planIx) (VarE nextStart))
          ]

    fieldInLocVar i = fieldNm "in_loc" i
    fieldOutLocVar i = fieldNm "out_loc" i
    fieldOutEndLocVar i = fieldNm "out_end_loc" i
    fieldOutCurVar i = fieldNm "out_cur_pre" i
    fieldOutEndVar i = fieldNm "out_end" i
    fieldReqBytesVar i = fieldNm "req_bytes" i
    fieldReqEndVar i = fieldNm "req_end" i
    fieldFitsVar i = fieldNm "fits" i

    indexCursorExp arr ix = Ext $ IndexCursorArray arr ix

    mkAllAnd :: [Exp3] -> Exp3
    mkAllAnd [] = PrimAppE MkTrue []
    mkAllAnd [e] = e
    mkAllAnd (e:es) = PrimAppE AndP [e, mkAllAnd es]

    substFieldValue :: Exp3 -> Var -> Exp3
    substFieldValue ex newV =
      case S.toList (gFreeVars ex) of
        [] -> ex
        [v] -> substE (VarE v) (VarE newV) ex
        _ -> ex

extractFieldPlans :: DataCon -> [Ty3] -> Exp3 -> Maybe [FieldPlan]
extractFieldPlans recDCon scalarTys bod = do
  (_, branches) <- findTopCase bod
  recBranch <- lookup recDCon [ (dcon, rhs) | (dcon, _, rhs) <- branches ]
  let binds = collectLeadingLets recBranch
      scalarInputs = collectScalarInputs binds
      env = collectPureBindings scalarInputs binds
      writes =
        [ (s, normalizePureExpr env rhs)
        | (_, _, _, Ext (WriteScalar s _ rhs)) <- binds
        ]
  if length writes /= length scalarTys
    then Nothing
    else sequence $
           zipWith
             (\ty (s, rhs) -> do
                 let rhs' = rhs
                     fvs = gFreeVars rhs'
                 if not (fvs `S.isSubsetOf` S.fromList (M.keys scalarInputs))
                   then Nothing
                   else if length (S.toList fvs) > 1
                          then Nothing
                          else if scalarToTy s /= ty
                                 then Nothing
                                 else Just FieldPlan { fpScalar = s, fpExpr = rhs' })
             scalarTys
             writes

findTopCase :: Exp3 -> Maybe (Exp3, [(DataCon, [(Var, ())], Exp3)])
findTopCase ex =
  case ex of
    LetE (_, _, _, _) bod -> findTopCase bod
    CaseE scrt brs -> Just (scrt, brs)
    _ -> Nothing

collectLeadingLets :: Exp3 -> [(Var, [()], Ty3, Exp3)]
collectLeadingLets ex =
  case ex of
    LetE b bod -> b : collectLeadingLets bod
    _ -> []

collectScalarInputs :: [(Var, [()], Ty3, Exp3)] -> M.Map Var Scalar
collectScalarInputs binds = goTuple M.empty M.empty binds
  where
    goTuple _ acc [] = acc
    goTuple tupleMap acc ((v, _, _, rhs):rest) =
      case rhs of
        Ext (ReadScalar s _) ->
          let tupleMap' = M.insert v s tupleMap
           in goTuple tupleMap' acc rest
        ProjE 0 (VarE tup) ->
          case M.lookup tup tupleMap of
            Just s -> goTuple tupleMap (M.insert v s acc) rest
            Nothing -> goTuple tupleMap acc rest
        _ -> goTuple tupleMap acc rest

collectPureBindings :: M.Map Var Scalar -> [(Var, [()], Ty3, Exp3)] -> M.Map Var Exp3
collectPureBindings scalarInputs = go M.empty
  where
    go env [] = env
    go env ((v, _, _, rhs):rest)
      | v `M.member` scalarInputs = go env rest
      | otherwise =
          case normalizePureExpr env rhs of
            rhs'
              | isSupportedPureExpr rhs' ->
                  go (M.insert v rhs' env) rest
            _ -> go env rest

normalizePureExpr :: M.Map Var Exp3 -> Exp3 -> Exp3
normalizePureExpr env ex =
  case ex of
    VarE v -> fromMaybe (VarE v) (M.lookup v env)
    LitE{} -> ex
    CharE{} -> ex
    FloatE{} -> ex
    LitSymE{} -> ex
    PrimAppE p args -> PrimAppE p (map (normalizePureExpr env) args)
    IfE a b c -> IfE (normalizePureExpr env a) (normalizePureExpr env b) (normalizePureExpr env c)
    ProjE i e -> ProjE i (normalizePureExpr env e)
    _ -> ex

isSupportedPureExpr :: Exp3 -> Bool
isSupportedPureExpr ex =
  case ex of
    VarE{} -> True
    LitE{} -> True
    CharE{} -> True
    FloatE{} -> True
    LitSymE{} -> True
    PrimAppE _ args -> all isSupportedPureExpr args
    IfE a b c -> all isSupportedPureExpr [a, b, c]
    ProjE _ e -> isSupportedPureExpr e
    _ -> False

collectMentionedDataCons :: Exp3 -> [DataCon]
collectMentionedDataCons ex =
  case ex of
    VarE{} -> []
    LitE{} -> []
    CharE{} -> []
    FloatE{} -> []
    LitSymE{} -> []
    AppE _ _ _ args -> concatMap collectMentionedDataCons args
    PrimAppE _ args -> concatMap collectMentionedDataCons args
    LetE (_, _, _, rhs) bod ->
      collectMentionedDataCons rhs ++ collectMentionedDataCons bod
    IfE a b c ->
      collectMentionedDataCons a
        ++ collectMentionedDataCons b
        ++ collectMentionedDataCons c
    MkProdE ls -> concatMap collectMentionedDataCons ls
    ProjE _ e -> collectMentionedDataCons e
    CaseE scrt brs ->
      collectMentionedDataCons scrt
        ++ concatMap
          (\(dcon, _, rhs) -> dcon : collectMentionedDataCons rhs)
          brs
    DataConE _ dcon args -> dcon : concatMap collectMentionedDataCons args
    TimeIt e _ _ -> collectMentionedDataCons e
    WithArenaE _ e -> collectMentionedDataCons e
    SpawnE _ _ args -> concatMap collectMentionedDataCons args
    SyncE -> []
    MapE (_, _, e1) e2 ->
      collectMentionedDataCons e1 ++ collectMentionedDataCons e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      collectMentionedDataCons e1
        ++ collectMentionedDataCons e2
        ++ collectMentionedDataCons e3
    Ext ext ->
      case ext of
        ReadScalar{} -> []
        WriteScalar _ _ rhs -> collectMentionedDataCons rhs
        ReadTag{} -> []
        WriteTag dcon _ -> [dcon]
        WriteTagPacked _ rhs -> collectMentionedDataCons rhs
        TagCursor{} -> []
        WriteCursorIndirection{} -> []
        WriteTaggedCursor _ rhs -> collectMentionedDataCons rhs
        MemCpy{} -> []
        ReadTaggedCursor{} -> []
        ReadCursor{} -> []
        GrowRegion{} -> []
        WriteCursorMutable _ rhs -> collectMentionedDataCons rhs
        ReadList{} -> []
        WriteList _ rhs _ -> collectMentionedDataCons rhs
        ReadVector{} -> []
        WriteVector _ rhs _ -> collectMentionedDataCons rhs
        MakeCursorArray{} -> []
        IndexCursorArray{} -> []
        AddCursor _ rhs -> collectMentionedDataCons rhs
        BumpCursorMutable _ rhs -> collectMentionedDataCons rhs
        AddrOfCursor rhs -> collectMentionedDataCons rhs
        DerefMutCursor{} -> []
        CastPtr{} -> []
        SubPtr{} -> []
        NewBuffer{} -> []
        ScopedBuffer{} -> []
        NewParBuffer{} -> []
        ScopedParBuffer{} -> []
        EndOfBuffer{} -> []
        MMapFileSize{} -> []
        SizeOfPacked{} -> []
        SizeOfScalar{} -> []
        BoundsCheck{} -> []
        BoundsCheckVector{} -> []
        IndirectionBarrier{} -> []
        BumpArenaRefCount{} -> []
        NullCursor -> []
        InitCursor{} -> []
        RetE ls -> concatMap collectMentionedDataCons ls
        GetCilkWorkerNum -> []
        LetAvail _ bod -> collectMentionedDataCons bod
        AllocateTagHere{} -> []
        AllocateScalarsHere{} -> []
        StartTagAllocation{} -> []
        EndTagAllocation{} -> []
        StartScalarsAllocation{} -> []
        EndScalarsAllocation{} -> []
        ScalarCountBump dcon _ -> [dcon]
        ReadScalarCount{} -> []
        ReadScalarCountFirstFooter{} -> []
        ReadScalarCountNextFooter{} -> []
        ForE _ bound bod ->
          collectMentionedDataCons bound ++ collectMentionedDataCons bod
        WhileCursor _ bod -> collectMentionedDataCons bod
        SSPush{} -> []
        SSPop{} -> []
        Assert rhs -> collectMentionedDataCons rhs
