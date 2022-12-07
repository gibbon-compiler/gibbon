{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Interpreter reducing L2 programs to values.
module Gibbon.L2.Interp -- ( interpProg, interp )
where

import           Control.DeepSeq
import           Control.Monad.Writer
import           Control.Monad.State
import           Data.ByteString.Builder (Builder, toLazyByteString, string8)
import           Data.Foldable (foldlM)
import           System.Clock
import           Text.PrettyPrint.GenericPretty
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Sequence as S
import           Data.Sequence (Seq, ViewL(..))
import           Data.Word (Word8)
import           Data.Char ( ord )
import           Data.Foldable as F
import           Data.Maybe ( fromJust )

import           Gibbon.Common
import           Gibbon.Passes.Lower ( getTagOfDataCon )
import qualified Gibbon.L1.Interp as L1
import           Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

instance Interp Store Exp2 where
  gInterpExp rc valenv ddefs fenv ext = fst <$> interp M.empty rc valenv ddefs fenv ext

instance InterpExt Store Exp2 (E2Ext LocVar Ty2) where
  gInterpExt rc valenv ddefs fenv ext = fst <$> interpExt M.empty rc valenv ddefs fenv ext

instance InterpProg Store Exp2 where
  gInterpProg store rc Prog{ddefs,fundefs,mainExp} =
      case mainExp of
        -- Print nothing, return "void"
        Nothing -> return (store, VProd [], B.empty)
        Just (e,_) -> do
          let fenv = M.fromList [ (funName f , f) | f <- M.elems fundefs]
          ((v, _size),logs,store1) <- runInterpM (interp M.empty rc M.empty ddefs fenv e) store
          -- Policy: don't return locations
          let res = case v of
                        (VLoc reg off) ->
                            let buf = fromJust $ lookupInStore' reg store1
                            in deserialize ddefs store1 (dropInBuffer off buf)
                        oth -> oth
          pure (store1, res, toLazyByteString logs)


--------------------------------------------------------------------------------

interp :: SizeEnv -> RunConfig -> ValEnv Exp2 -> DDefs Ty2 -> M.Map Var (FunDef Exp2)
       -> Exp2 -> InterpM Store Exp2 (Value Exp2, Size)
interp szenv rc valenv ddefs fenv e = go valenv szenv e
  where
    {-# NOINLINE goWrapper #-}
    goWrapper !_ix env sizeEnv ex = go env sizeEnv ex

    go :: ValEnv Exp2 -> SizeEnv -> Exp2 -> InterpM Store Exp2 (Value Exp2, Size)
    go env sizeEnv ex =
      case ex of
        -- We interpret a function application by substituting the operand (at
        -- the call-site) for the function argument in the environment. Since
        -- this is a L2 program, we have real locations (and regions) and we
        -- have to make sure that those get passed in as well. We do that
        -- by extending the environment with the location at the call-site.
        --
        -- TODO: After ThreadRegions, even regions are passed in the locs
        -- field. Need to extend the environment with some kind of region
        -- value as well. Also, since we're storing regions in the value
        -- environment anyways, we probably don't need an additional store.
        --
        AppE f locs args ->
          case M.lookup f fenv of
            Nothing -> error $ "L2.Interp: unbound function: "++sdoc ex
            Just FunDef{funArgs,funBody,funTy} -> do
              (rands,szs) <- unzip <$> mapM (go env sizeEnv) args
              let inLocs  = inLocVars funTy
                  outLocs = outLocVars funTy
                  -- ASSUMPTION: Ordering is important in `locs`, and we assume
                  -- that the input locations appear before output locations.
                  env' = foldr
                           (\(fnLoc, callSiteLoc) acc ->
                              M.insert fnLoc (acc M.! callSiteLoc)  acc)
                           env
                           (zip (inLocs ++ outLocs) locs)
              go (M.union (M.fromList $ zip funArgs rands) env')
                 (M.union (M.fromList $ zip funArgs szs) sizeEnv)
                 funBody

        CaseE _ [] -> error $ "L2.Interp: Empty case"
        CaseE x1 alts -> do
          (scrt, _sizescrt) <- go env sizeEnv x1
          dbgTraceIt (sdoc (x1,scrt,env,sizeEnv)) (pure ())
          case scrt of
            VLoc idx off ->
               do (Store store) <- get
                  let Buffer seq1 = store M.! idx
                  case S.viewl (S.drop off seq1) of
                    S.EmptyL -> error "L1.Interp: case scrutinize on empty/out-of-bounds location."
                    SerTag _tg datacon :< _rst -> do
                      let -- tycon = getTyOfDataCon ddefs datacon
                          (_dcon,vlocs,rhs) = lookup3 (dbgTrace 3 (show datacon ++ "\n" ++ show alts) $ datacon) alts
                          tys = lookupDataCon ddefs datacon
                      (env', sizeEnv', _off') <- foldlM
                                (\(aenv, asizeEnv, prev_off) ((v,loc), ty) -> do
                                    case ty of
                                      -- Just skip past random access nodes.
                                      CursorTy -> do
                                          let sizeloc = fromJust $ byteSizeOfTy CursorTy
                                              aenv' = M.insert loc (VLoc idx prev_off) aenv
                                              asizeEnv' = M.insert loc (SOne sizeloc) asizeEnv
                                          pure (aenv', asizeEnv', prev_off + sizeloc)
                                      -- Traverse this value to find it's end-witness and use
                                      -- it to bind the value after this one.
                                      PackedTy pkd_tycon _ -> do
                                          let current_val = VLoc idx prev_off
                                              aenv' = M.insert v current_val $
                                                      M.insert loc current_val $
                                                      aenv
                                          let trav_fn = mkTravFunName pkd_tycon
                                          -- Bind v to (SOne -1) in sizeEnv temporarily, just long enough
                                          -- to evaluate the call to trav_fn.
                                          (_, sizev) <- go aenv' (M.insert v (SOne (-1)) sizeEnv) (AppE trav_fn [loc] [VarE v])
                                          let sizeloc = fromJust $ byteSizeOfTy CursorTy
                                              asizeEnv' = M.insert v sizev $
                                                          M.insert loc (SOne sizeloc) $
                                                          asizeEnv
                                          dbgTraceIt (sdoc (v, prev_off, sizev, prev_off + 1 + (sizeToInt sizev))) (pure ())
                                          pure (aenv', asizeEnv', prev_off + (sizeToInt sizev))
                                      scalarty | isScalarTy scalarty -> do
                                        s@(Store store1) <- get
                                        let buf = store1 M.! idx
                                            val  = deserialize ddefs s (dropInBuffer prev_off buf)
                                            aenv' = M.insert v val $
                                                    M.insert loc (VLoc idx prev_off) $
                                                    aenv
                                            size = (fromJust $ byteSizeOfTy scalarty)
                                            asizeEnv' = M.insert v (SOne size) asizeEnv
                                        pure (aenv', asizeEnv', prev_off + size)
                                      _ -> error $ "L2.Interp: TODO: " ++ sdoc ty)
                                (env, sizeEnv, off+1)
                                (zip vlocs tys)
                      go env' sizeEnv' rhs
                    oth :< _ -> error $ "L2.Interp: expected to read tag from scrutinee cursor, found: "++show oth++
                                        ".\nRead " ++ sdoc scrt ++ " in buffer: " ++ sdoc seq1
            _ -> error $ "L2.Interp: expected scrutinee to be a packed value. Got: " ++ sdoc scrt

        -- This operation constructs a packed value by writing things to the
        -- buffer. The packed value is represented by a 1 byte tag,
        -- followed by other arguments.
        DataConE loc dcon args ->
          case M.lookup loc env of
            Nothing -> error $ "L2.Interp: Unbound location: " ++ sdoc loc
            Just (VLoc reg offset) -> do
              buf_maybe <- lookupInStore reg
              case buf_maybe of
                Nothing  -> error $ "L2.Interp: Unbound region " ++ sdoc reg
                Just buf -> do
                  vals <- mapM (go env sizeEnv) args
                  let tys = lookupDataCon ddefs dcon
                      tag = getTagOfDataCon ddefs dcon
                      bufWithTag = insertAtBuffer offset (SerTag tag dcon) buf
                      (bufWithVals, new_off) =
                        foldl
                          (\(acc, off) ((v, sz), _ty) ->
                               let new_off1 = off + sizeToInt sz
                                   f v2 =
                                     case v2 of
                                       VInt i -> ( insertAtBuffer off (SerInt i) acc , new_off1 )
                                       VChar i -> ( insertAtBuffer off (SerChar i) acc , new_off1 )
                                       VFloat{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VSym{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VBool{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       -- This is a packed value, and it must already
                                       -- be written to the buffer (by the thing that
                                       -- returned this). So we just update the offset
                                       -- to point to the end of this value.
                                       VLoc{} -> ( acc , new_off1 )
                                       VPtr buf_id off1 -> ( insertAtBuffer off (SerPtr buf_id off1) acc, new_off1)
                                       VDict{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VProd{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VList{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VPacked{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VCursor{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VLam{} -> error $ "L2.Interp: DataConE todo" ++ sdoc v2
                                       VWrapId _id2 v3 -> f v3
                               in f v
                          )
                          (bufWithTag, offset+1)
                          (zip vals tys)
                  insertIntoStore reg bufWithVals
                  return (VLoc reg offset, SOne (new_off - offset))
            Just val -> error $ "L2.Interp: Unexpected value for " ++ sdoc loc ++ ":" ++ sdoc val

        -- Ignoring end-witnesses atm.
        LetE (v,_locs,_ty,rhs) bod -> do
          (rhs', sz) <- go env sizeEnv rhs
          go (M.insert v rhs' env) (M.insert v sz sizeEnv) bod
        -- Straightforward recursion (same as the L1 interpreter)
        Ext ext -> interpExt sizeEnv rc env ddefs fenv ext
        LitE n    -> return (VInt n, SOne (fromJust $ byteSizeOfTy IntTy))
        CharE n   -> return (VChar n, SOne (fromJust $ byteSizeOfTy CharTy))
        FloatE n  -> return (VFloat n, SOne (fromJust $ byteSizeOfTy FloatTy))
        LitSymE s -> return (VInt (strToInt $ fromVar s),
                             SOne (fromJust $ byteSizeOfTy SymTy))
        VarE v    -> return (env # v, sizeEnv # v)

        PrimAppE p args -> do
            (args',_) <- unzip <$> mapM (go env sizeEnv) args
            case byteSizeOfTy (primRetTy p) of
              Just sz -> do
                  val <- L1.applyPrim rc p args'
                  pure (val, SOne sz)
              Nothing -> error $ "L2.Interp: Couldn't guess the size: " ++ sdoc ex

        IfE a b c -> do (v,_) <- go env sizeEnv a
                        case v of
                         VBool flg -> if flg
                                      then go env sizeEnv b
                                      else go env sizeEnv c
                         oth -> error$ "interp: expected bool, got: "++show oth

        MkProdE ls -> do
            (args, szs) <- unzip <$> mapM (go env sizeEnv) ls
            return (VProd args , SMany szs)

        ProjE ix e0 -> do
            val <- go env sizeEnv e0
            case val of
              (VProd ls, SMany szs) -> return (ls !! ix, szs !! ix)
              (VProd ls, SOne sz)   -> return (ls !! ix, SOne sz)
              oth -> error $ "L2.Interp: expected VProd, got: " ++ sdoc (ex, oth)

        TimeIt bod _ isIter -> do
              let iters = if isIter then rcIters rc else 1
              !_ <- return $! force env
              st <- liftIO $ getTime clk
              (val,sz) <- foldM (\ _ i -> goWrapper i env sizeEnv bod)
                            (error "Internal error: this should be unused.")
                          [1..iters]
              en <- liftIO $ getTime clk
              let tm = fromIntegral (toNanoSecs $ diffTimeSpec en st)
                        / 10e9 :: Double
              if isIter
               then do tell$ string8 $ "ITERS: "++show iters       ++"\n"
                       tell$ string8 $ "SIZE: " ++show (rcSize rc) ++"\n"
                       tell$ string8 $ "BATCHTIME: "++show tm      ++"\n"
               else tell$ string8 $ "SELFTIMED: "++show tm ++"\n"
              return $! (val, sz)

        SpawnE f locs args -> go env sizeEnv (AppE f locs args)
        SyncE -> pure $ (VInt (-1), SOne 0)

        WithArenaE{} -> error "L2.Interp: WithArenE not handled"

        MapE{} -> error $ "L2.Interp: TODO " ++ sdoc ex
        FoldE{} -> error $ "L2.Interp: TODO " ++ sdoc ex

{-
          DataConE _ k ls -> do
              args <- mapM (go env) ls
              return $ VPacked k args
              -- Constructors are overloaded.  They have different behavior depending on
              -- whether we are AFTER Cursorize or not.
              case args of
                [ VCursor idx off ] | rcCursors rc ->
                    do Store store <- get
                       let tag       = SerTag (getTagOfDataCon ddefs k) k
                           store'    = IM.alter (\(Just (Buffer s1)) -> Just (Buffer $ s1 |> tag)) idx store
                       put (Store store')
                       return $ VCursor idx (off+1)
                _ -> return $ VPacked k args


-}

interpExt :: SizeEnv -> RunConfig -> ValEnv Exp2 -> DDefs Ty2 -> M.Map Var (FunDef Exp2)
           -> E2Ext LocVar Ty2 -> InterpM Store Exp2 (Value Exp2, Size)
interpExt sizeEnv rc env ddefs fenv ext =
  case ext of
    LetRegionE reg _ _ bod -> do
      insertIntoStore (regionToVar reg) emptyBuffer
      go env sizeEnv bod

    LetParRegionE reg sz ty bod ->
      interpExt sizeEnv rc env ddefs fenv (LetRegionE reg sz ty bod)

    LetLocE loc locexp bod ->
      case locexp of
        StartOfRegionLE reg -> do
          buf_maybe <- lookupInStore (regionToVar reg)
          case buf_maybe of
            Nothing -> error $ "L2.Interp: Unbound region: " ++ sdoc reg
            Just _ ->
              go (M.insert loc (VLoc (regionToVar reg) 0) env) sizeEnv bod

        AfterConstantLE i loc2 -> do
          case M.lookup loc2 env of
            Nothing -> error $ "L2.Interp: Unbound location: " ++ sdoc loc2
            Just (VLoc reg offset) ->
              go (M.insert loc (VLoc reg (offset + i)) env) sizeEnv bod
            Just val ->
              error $ "L2.Interp: Unexpected value for " ++ sdoc loc2 ++ ":" ++ sdoc val

        AfterVariableLE v loc2 _ -> do
          case M.lookup loc2 env of
            Nothing -> error $ "L2.Interp: Unbound location: " ++ sdoc loc2
            Just (VLoc reg offset) ->
              case M.lookup v sizeEnv of
                Nothing -> error $ "L2.Interp: No size info found: " ++ sdoc v
                Just sz ->
                  go (M.insert loc (VLoc reg (offset + (sizeToInt sz))) env)
                     sizeEnv bod
            Just val ->
              error $ "L2.Interp: Unexpected value for " ++ sdoc loc2 ++ ":" ++ sdoc val

        FromEndLE{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
        InRegionLE{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
        FreeLE{} -> error $ "L2.Interp: TODO: " ++ sdoc ext


    -- Ignoring end-witnesses atm.
    StartOfPkd{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    TagCursor{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    RetE _locs v -> return (env # v, sizeEnv # v)
    FromEndE{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    BoundsCheck{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    AddFixed{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    IndirectionE{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    GetCilkWorkerNum{} -> pure $ (VInt 1, SOne (fromJust $ byteSizeOfTy IntTy))
    LetAvail{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    AllocateTagHere{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    AllocateScalarsHere{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    SSPush{} -> error $ "L2.Interp: TODO: " ++ sdoc ext
    SSPop{} -> error $ "L2.Interp: TODO: " ++ sdoc ext

  where
    go valenv szenv = interp szenv rc valenv ddefs fenv


clk :: Clock
clk = Monotonic

strToInt :: String -> Int
strToInt = product . map ord

--------------------------------------------------------------------------------
-- Stores and buffers:
--------------------------------------------------------------------------------

-- | A store is an address space full of buffers.
newtype Store = Store (M.Map Var Buffer)
  deriving (Read, Show, Eq, Ord, Generic, Out)

emptyStore :: Store
emptyStore = Store M.empty

insertIntoStore :: Var -> Buffer -> InterpM Store Exp2 ()
insertIntoStore v buf = modify (\(Store x) -> Store (M.insert v buf x))

lookupInStore :: Var -> InterpM Store Exp2 (Maybe Buffer)
lookupInStore v = do
  Store store <- get
  return $ M.lookup v store

lookupInStore' :: Var -> Store -> Maybe Buffer
lookupInStore' reg (Store mp) = M.lookup reg mp

newtype Buffer = Buffer (Seq SerializedVal)
  deriving (Read, Show, Eq, Ord, Generic, Out)

emptyBuffer :: Buffer
emptyBuffer = Buffer S.empty

-- | Insert a value at a particular index in the buffer
insertAtBuffer :: Int -> SerializedVal -> Buffer -> Buffer
insertAtBuffer i v (Buffer b) =
    if expected_size == 1
    then Buffer b'
    -- We must make 'v' occupy 'expected_size' number of cells in the buffer.
    else
      let pad = expected_size - 1
          b'' = foldl (\acc j -> S.insertAt (i+j) SerPad acc) b' [1..pad]
      in Buffer b''
  where
    expected_size = byteSize v
    b' = S.insertAt i v b

dropInBuffer :: Int -> Buffer -> Buffer
dropInBuffer off (Buffer ls) = Buffer (S.drop off ls)

data SerializedVal
    = SerTag Word8 DataCon
    | SerInt Int
    | SerChar Char
    | SerBool Int
    | SerFloat Double
    | SerPtr { bufID :: Var, offset :: Int }
    | SerPad
    -- ^ Used to make values artificially occupy more cells in the buffer.
    -- For example, everywhere else we assume that Ints occupy 8 cells.
    -- But 'SerInt' only occupies a single cell. To make 'SerInt' occupy 8
    -- cells, we add 7 'SerPad's after it.
  deriving (Read, Show, Eq, Ord, Generic, Out, NFData)

-- Must match with sizes returned by 'byteSizeOfTy'.
byteSize :: SerializedVal -> Int
byteSize (SerTag{})   = 1
byteSize (SerBool{})  = 1
byteSize (SerPad)     = 1
byteSize (SerInt{})   = 8
byteSize (SerChar{})  = 1
byteSize (SerFloat{}) = 8
byteSize (SerPtr{})   = 8

-- | Everything occupies a single cell in the 'Buffer'.
byteSizeOfTy :: UrTy d -> Maybe Int
byteSizeOfTy = sizeOfTy

instance Out a => Out (Seq a) where
  doc s       = doc       (F.toList s)
  docPrec n s = docPrec n (F.toList s)

-- | Code to read a final answer back out.
deserialize :: (Out ty) => DDefs ty -> Store -> Buffer -> Value Exp2
deserialize ddefs store (Buffer seq0) = final
 where
  ([final],_) = readN 1 seq0

  readN 0 seq1 = ([],seq1)
  readN n seq1 =
     case S.viewl seq1 of
       S.EmptyL -> error $ "deserialize: unexpected end of sequence: "++ndoc seq0
       SerInt i :< rst ->
         let (more,rst') = readN (n-1) rst
         in (VInt i : more, rst')

       SerBool i :< rst ->
         let (more,rst') = readN (n-1) rst
             -- 1 is True
             b = i /= 0
         in (VBool b : more, rst')

       SerTag _ k :< rst ->
         let (args,rst')  = readN (length (lookupDataCon ddefs k)) rst
             (more,rst'') = readN (n-1) rst'
         in (VPacked k args : more, rst'')

       SerFloat i :< rst ->
         let (more,rst') = readN (n-1) rst
         in (VFloat i : more, rst')

       SerPtr buf_id off :< rst ->
         let Store s = store
             Buffer pointee = dropInBuffer off (s M.! buf_id)
             (ls, _rst') = readN n pointee
         in (ls, rst)

       SerPad :< rst ->
         readN n rst
         -- let (more,rst') = readN (n-1) rst
         -- in (VInt (-1) : more, rst')

data Size = SOne Int
          | SMany [Size]
  deriving (Read, Show, Eq, Ord, Generic, Out)

type SizeEnv = M.Map Var Size

sizeToInt :: Size -> Int
sizeToInt (SOne i)   = i
sizeToInt (SMany ls) = sum $ map sizeToInt ls

appendSize :: Size -> Size -> Size
appendSize a b =
    case (a,b) of
        (SOne i, SOne j)     -> SOne (i+j)
        (SMany xs, SMany ys) -> SMany (xs ++ ys)
        (x, SMany xs) -> SMany (x:xs)
        (SMany xs, x) -> SMany (xs++[x])
