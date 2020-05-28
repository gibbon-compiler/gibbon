{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-------------------------------------------------------------------------------

-- | Lowering L3 to the target language.
module Gibbon.Passes.Lower
  ( lower, getTagOfDataCon
  ) where

-------------------------------------------------------------------------------

import           Control.Monad
import           Data.Foldable
import           Data.Maybe
import           Data.List as L hiding (tail)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Int (Int64)
import           Data.Word (Word16)
import           Data.Tuple (swap)
import           Prelude hiding (tail)
import           Text.PrettyPrint.GenericPretty
import qualified Data.List as L

import           Gibbon.Common
import           Gibbon.DynFlags
import           Gibbon.L3.Syntax
import qualified Gibbon.L3.Syntax as L3
import qualified Gibbon.L4.Syntax as T

-- Generating unpack functions from Packed->Pointer representation:
-------------------------------------------------------------------------------

genDcons :: [Ty3] -> Var -> [(T.Ty, T.Triv)] -> PassM T.Tail
genDcons (x:xs) tail fields = case x of
  PackedTy tyCons _ -> do
    ptr  <- gensym  "ptr"
    t    <- gensym  "tail"
    T.LetCallT False [(ptr, T.PtrTy), (t, T.CursorTy)] (mkUnpackerName tyCons) [(T.VarTriv tail)]
      <$> genDcons xs t (fields ++ [(T.CursorTy, T.VarTriv ptr)])

  -- Int, Float, Sym or Bool
  _ | isScalarTy x ->  do
    val  <- gensym "val"
    t    <- gensym "tail"
    let l4_ty = T.fromL3Ty x
    T.LetPrimCallT [(val, l4_ty), (t, T.CursorTy)] (T.ReadScalar (mkScalar x)) [(T.VarTriv tail)]
      <$> genDcons xs t (fields ++ [(l4_ty, T.VarTriv val)])

  VectorTy el_ty -> do
    val <- gensym "val"
    t   <- gensym "tail"
    let l4_ty = T.fromL3Ty el_ty
    T.LetPrimCallT [(val, T.VectorTy l4_ty), (t, T.CursorTy)] T.ReadList [(T.VarTriv tail)]
      <$> genDcons xs t (fields ++ [(l4_ty, T.VarTriv val)])

  -- Indirection or redirection pointer
  CursorTy -> do
    next <- gensym "next"
    afternext <- gensym "afternext"
    let l4_ty = T.fromL3Ty x
    T.LetPrimCallT [(next, T.CursorTy),(afternext,T.CursorTy)] T.ReadCursor [(T.VarTriv tail)] <$>
      genDcons xs afternext (fields ++ [(l4_ty, T.VarTriv next)])

  _ -> error $ "genDcons: FIXME " ++ show x

genDcons [] tail fields     = do
  ptr <- gensym "ptr"
  return $ T.LetAllocT ptr fields $ T.RetValsT [T.VarTriv ptr, T.VarTriv tail]

genAlts :: [(DataCon,[(IsBoxed,Ty3)])] -> Var -> Var -> Int64 -> PassM T.Alts
-- Don' do anything for indirections. Let 'followRedirects' take care of it.
genAlts ((dcons, _):rst) tail tag n | isIndirectionTag dcons = genAlts rst tail tag n
genAlts ((_dcons, typs):xs) tail tag n = do
  let (_,typs') = unzip typs
  -- WARNING: IsBoxed ignored here
  curTail <- genDcons typs' tail [(T.TagTyPacked, T.VarTriv tag)]
  alts    <- genAlts xs tail tag (n+1)
  let alt = n
  case alts of
    T.IntAlts []   -> return $ T.IntAlts [(alt::Int64, curTail)]
    -- T.TagAlts []   -> return $ T.TagAlts [(n::Word8, curTail)]
    T.IntAlts tags -> return $ T.IntAlts ((alt::Int64, curTail) : tags)
    -- T.TagAlts tags -> return $ T.TagAlts ((n::Word8, curTail) : tags)
    _              -> error $ "Invalid case statement type."

genAlts [] _ _ _                  = return $ T.IntAlts []

genUnpacker :: DDef Ty3 -> PassM T.FunDecl
genUnpacker DDef{tyName, dataCons} = do
  p    <- gensym "p"
  tag  <- gensym "tag"
  tail <- gensym "tail"
  alts <- genAlts dataCons tail tag 0
  lbl  <- gensym "switch"
  let def_alt = T.ErrT $ "Unknown tag in: " ++ fromVar lbl
  bod  <- return $ T.LetPrimCallT [(tag, T.TagTyPacked), (tail, T.CursorTy)] T.ReadTag [(T.VarTriv p)] $
                   T.Switch lbl (T.VarTriv tag) alts (Just def_alt)
  return T.FunDecl{ T.funName  = mkUnpackerName (fromVar tyName),
                    T.funArgs  = [(p, T.CursorTy)],
                    T.funRetTy = T.ProdTy [T.PtrTy, T.CursorTy],
                    T.funBody  = bod,
                    T.isPure   = False
                  }


-- | Modify a Tail to *print* its return value and then

-- Utility functions
printString :: String -> (T.Tail -> T.Tail)
printString s = T.LetPrimCallT [] (T.PrintString s) []

openParen :: String -> (T.Tail -> T.Tail)
openParen s = printString $ "(" ++ s ++ " "

closeParen :: T.Tail -> T.Tail
closeParen   = printString ")"

printSpace :: T.Tail -> T.Tail
printSpace = printString " "

sandwich :: (T.Tail -> T.Tail) -> String -> T.Tail -> T.Tail
sandwich mid s end = openParen s $ mid $ closeParen end

-- Generate printing functions
genDconsPrinter :: [Ty3] -> Var -> PassM T.Tail
genDconsPrinter (x:xs) tail =
  case x of
    L3.PackedTy tyCons _ -> do
      dflags <- getDynFlags
      if gopt Opt_Packed dflags
      then do
        t    <- gensym "tail"
        T.LetCallT False [(t, T.CursorTy)] (mkPrinterName tyCons) [(T.VarTriv tail)] <$>
           maybeSpace <$> genDconsPrinter xs t
      else do
        val  <- gensym "val"
        t    <- gensym "tail"
        tmp  <- gensym "temp"
        valc <- gensym "valcur"
        T.LetPrimCallT [(val, T.IntTy), (t, T.CursorTy)] (T.ReadScalar IntS) [(T.VarTriv tail)] <$>
          T.LetTrivT (valc, T.CursorTy, T.VarTriv val) <$>
          T.LetCallT False [(tmp, T.CursorTy)] (mkPrinterName tyCons) [(T.VarTriv valc)] <$>
            maybeSpace <$> genDconsPrinter xs t

    L3.CursorTy -> do
      dflags <- getDynFlags
      if gopt Opt_Packed dflags
      then do
        tail2 <- gensym "tail"
        T.LetPrimCallT [(tail2, T.CursorTy)] T.AddP [T.VarTriv tail, T.IntTriv 8] <$>
          genDconsPrinter xs tail2
      else genDconsPrinter xs tail

    _ | isScalarTy x ->  do
      val  <- gensym "val"
      t    <- gensym "tail"
      let l4_ty = T.fromL3Ty x
      T.LetPrimCallT [(val, l4_ty), (t, T.CursorTy)] (T.ReadScalar (mkScalar x)) [(T.VarTriv tail)] <$>
        printTy False x [T.VarTriv val] <$>
         maybeSpace <$>
          genDconsPrinter xs t

    VectorTy el_ty ->  do
      val  <- gensym "val"
      t    <- gensym "tail"
      let l4_ty = T.fromL3Ty el_ty
      T.LetPrimCallT [(val, T.VectorTy l4_ty), (t, T.CursorTy)] T.ReadList [(T.VarTriv tail)] <$>
        printTy False x [T.VarTriv val] <$>
         maybeSpace <$>
          genDconsPrinter xs t

    _ -> error "FINISHME: genDconsPrinter"

 where
  maybeSpace = if L.null xs
               then id
               else printSpace

genDconsPrinter [] tail     = do
  return $ closeParen $ T.RetValsT [(T.VarTriv tail)]

genAltPrinter :: [(DataCon,[(IsBoxed, Ty3)])] -> Var -> Int64 -> PassM T.Alts
-- Don' do anything for indirections. Let 'followRedirects' take care of it.
genAltPrinter ((dcons, _):rst) tail n | isIndirectionTag dcons = genAltPrinter rst tail n
genAltPrinter ((dcons, typs):xs) tail n = do
  let (_,typs') = unzip typs
  -- WARNING: IsBoxed ignored here
  curTail <- (openParen dcons) <$> genDconsPrinter typs' tail
  alts    <- genAltPrinter xs tail (n+1)
  let alt = n
  case alts of
    T.IntAlts []   -> return $ T.IntAlts [(alt::Int64, curTail)]
    -- T.TagAlts []   -> return $ T.TagAlts [(n::Word8, curTail)]
    T.IntAlts tags -> return $ T.IntAlts ((alt::Int64, curTail) : tags)
    -- T.TagAlts tags -> return $ T.TagAlts ((n::Word8, curTail) : tags)
    _              -> error $ "Invalid case statement type."
genAltPrinter [] _ _                = return $ T.IntAlts []

genPrinter  :: DDef Ty3 -> PassM T.FunDecl
genPrinter DDef{tyName, dataCons} = do
  p    <- gensym "p"
  tag  <- gensym "tag"
  tail <- gensym "tail"
  alts <- genAltPrinter dataCons tail 0
  lbl  <- gensym "switch"
  dflags <- getDynFlags
  let def_alt = T.ErrT $ "Unknown tag in: " ++ fromVar lbl
  let bod = if gopt Opt_Packed dflags
            then T.LetPrimCallT [(tag, T.TagTyPacked), (tail, T.CursorTy)] (T.ReadTag) [(T.VarTriv p)] $
                 T.Switch lbl (T.VarTriv tag) alts (Just def_alt)
            else T.LetPrimCallT [(tag, T.TagTyPacked), (tail, T.CursorTy)] (T.ReadScalar IntS) [(T.VarTriv p)] $
                 T.Switch lbl (T.VarTriv tag) alts (Just def_alt)
  return T.FunDecl{ T.funName  = mkPrinterName (fromVar tyName),
                    T.funArgs  = [(p, T.CursorTy)],
                    T.funRetTy = T.CursorTy,
                    T.funBody  = bod,
                    T.isPure   = False
                  }

printTy :: Bool -> Ty3 -> [T.Triv] -> (T.Tail -> T.Tail)
printTy pkd ty trvs =
  case (ty, trvs) of
    (IntTy, [_one])             -> T.LetPrimCallT [] T.PrintInt trvs
    (FloatTy, [_one])           -> T.LetPrimCallT [] T.PrintFloat trvs
    (SymTy, [_one])             -> T.LetPrimCallT [] T.PrintSym trvs
    (SymDictTy _ ty', [_one])     -> sandwich (printTy pkd ty' trvs) "Dict"
    (PackedTy constr _, [one]) -> -- HACK: Using varAppend here was the simplest way to get
                                  -- unique names without using the PassM monad.
                                  -- ASSUMPTION: Argument (one) is always a variable reference.
                                  -- This is reasonable because the AST is always flattened before
                                  -- we try to lower it.
                                  -- But we should change this to use gensym anyways..
                                  let T.VarTriv v = one
                                      unpkd = varAppend "unpkd_" v
                                      ignre = varAppend "ignre_" v
                                  in
                                    if pkd
                                    then (\tl -> T.LetCallT False [(unpkd, T.PtrTy), (ignre, T.CursorTy)]
                                                 (mkUnpackerName constr) trvs $
                                                 T.LetCallT False [] (mkPrinterName constr) [T.VarTriv unpkd] tl)
                                    else T.LetCallT False [] (mkPrinterName constr) trvs
    (VectorTy{}, [_one]) -> T.LetPrimCallT [] (T.PrintString "<vector>") []

    (BoolTy, [trv]) ->
      let prntBool m = T.LetPrimCallT [] (T.PrintString m) []
      in \t -> T.IfT trv (prntBool truePrinted $ t) (prntBool falsePrinted $ t)

    (ProdTy tys, _) ->
      let printTupStart = printString "'#("
          (bltrvs,ltrv) = (init trvs, last trvs)
          (bltys,lty)   = (init tys, last tys)
      in \t ->
        printTupStart $
        foldr (\(ty,trv) acc -> printTy pkd ty [trv] $ printSpace acc)
        (printTy pkd lty [ltrv] $ closeParen t)
        (zip bltys bltrvs)
    _ -> error $ "printTy: unexpected: " ++ show (ty, trvs)


-- | In packed mode, keep only the start cursors for packed values
--
-- >>> properTrivs True  (Packedty Tree _) [start,end]
-- [start]
--
-- >>> properTrivs True (ProdTy [IntTy, PackedTy "Tree" _]) [val1, start_cursor_1, end_cursor_1]
-- [val1, start_cursor_1]
--
-- >>> properTrivs True (ProdTy [IntTy,PackedTy "Tree" _, IntTy, PackedTy "Tree _"])
--                 [val1, sc1, ec1, val2, sc2, ec2]
-- [val1, sc1, val2, sc2]
--
-- >>> properTrivs False (Packedty Tree _) [cur]
-- [cur]
--
-- >>> properTrivs False [IntTy,PackedTy "Tree" _, IntTy, PackedTy "Tree _"] [val1, c1, val2, c2]
-- [val1, c1, val2, c2]
properTrivs :: Bool -> Ty3 -> [T.Triv] -> [T.Triv]
properTrivs pkd ty trvs =
  if not pkd then trvs
  else
  case ty of
    ProdTy tys -> go [] tys trvs
    PackedTy{} -> init trvs
    _ -> trvs
  where
    go acc [] _trvs = acc
    go acc (ty:tys) (x:xs) =
      if isPackedTy ty
      then go (acc++[x]) tys (L.tail xs)
      else go (acc++[x]) tys xs
    go _ tys xs = error $ "properTrivs: unexpected tys and trvs: " ++ sdoc tys ++ " " ++ sdoc xs

-- printTy ty trvs = error $ "Invalid L3 data type; " ++ show ty ++ " " ++ show trvs

addPrintToTail :: Ty3 -> T.Tail-> PassM T.Tail
addPrintToTail ty tl0 = do
    dflags <- getDynFlags
    let pkd = gopt Opt_Packed dflags
        ty' = if pkd
              then T.IntTy
              else T.fromL3Ty ty
    T.withTail (tl0, ty') $ \ trvs ->
      printTy pkd ty (properTrivs pkd ty trvs) $
        -- Always print a trailing newline at the end of execution:
        T.LetPrimCallT [] (T.PrintString "\n") [] $
          T.LetPrimCallT [] T.FreeSymTable [] $
          T.RetValsT []  -- Void return after printing.

-- | Look up the numeric tag for a dataCon
getTagOfDataCon :: Out a => DDefs a -> DataCon -> Tag
getTagOfDataCon dds dcon =
    if isIndirectionTag dcon
    then indirectionAlt
    else if isRelRANDataCon dcon
    -- So that is_big in the RTS can identify which nodes have size information.
    then 150 + (fromIntegral ix)
    else fromIntegral ix
  where Just ix = L.elemIndex dcon $ getConOrdering dds (fromVar tycon)
        (tycon,_) = lkp dds dcon


-- The compiler pass
-------------------------------------------------------------------------------a

-- | Convert into the target language.  This does not make much of a
-- change, but it checks the changes that have already occurred.
--
-- The only substantitive conversion here is of tupled arguments to
-- multiple argument functions.
--
-- First argument indicates (1) whether we're inpacked mode, and (2)
-- the pre-cursorize type of the mainExp, if there is a mainExp.
lower :: Prog3 -> PassM T.Prog
lower Prog{fundefs,ddefs,mainExp} = do
  -- In Lower, we want to replace LitSymE's with the corresponding index into
  -- the symbol table. That's why we build a map from String's to Int64's.
  -- However, all the subsequent lookup's will be on the index, to get to the
  -- String. So we store an inverse of this map in a L4 program. Because we've
  -- built the map with `gensym`, it's safe to assume that the indices are
  -- unique.
  -- inv_sym_tbl :: M.Map String Word16
  inv_sym_tbl <- build_inv_symbol_table
  -- sym_tbl :: M.Map Int64 String
  let sym_tbl = M.fromList $ map swap (M.toList inv_sym_tbl)

  mn <- case mainExp of
          Nothing    -> return Nothing
          Just (x,mty) -> (Just . T.PrintExp) <$>
                            (addPrintToTail mty =<< tail inv_sym_tbl x)
  funs       <- mapM (fund inv_sym_tbl) (M.elems fundefs)
  unpackers  <- mapM genUnpacker (L.filter (not . isVoidDDef) (M.elems ddefs))
  printers   <- mapM genPrinter (L.filter (not . isVoidDDef) (M.elems ddefs))
  (T.Prog sym_tbl) <$> pure (funs ++ unpackers ++ printers) <*> pure mn
 where
  fund :: M.Map String Word16 -> FunDef3 -> PassM T.FunDecl
  fund sym_tbl FunDef{funName,funTy,funArgs,funBody} = do
      let (intys, outty) = funTy
      let (args, bod) = (zip funArgs (map typ intys), funBody)
      bod' <- tail sym_tbl bod
      return T.FunDecl{ T.funName  = funName
                      , T.funArgs  = args
                      , T.funRetTy = typ outty
                      , T.funBody  = bod'
                      , T.isPure   = ispure funBody
                      }

  -- TimeIt forms are impure because they have print statements after codegen
  ispure :: Exp3 -> Bool
  ispure ex =
    case ex of
      TimeIt{} -> False
      PrimAppE Gensym [] -> False
      PrimAppE RandP []  -> False
      PrimAppE FRandP []  -> False
      LetE (_,_,_,rhs) bod -> ispure rhs && ispure bod
      IfE _ b c   -> ispure b && ispure c
      CaseE _ brs -> all id $ L.map (\(_,_,rhs) -> ispure rhs) brs
      _ -> True

  build_inv_symbol_table :: PassM (M.Map String Word16)
  build_inv_symbol_table = foldrM (\s acc -> case M.lookup s acc of
                                           Just{}  -> pure acc
                                           Nothing -> do
                                             uniq <- fromIntegral <$> newUniq
                                             pure (M.insert s uniq acc))
                              M.empty all_syms
    where
      all_syms :: S.Set String
      all_syms = (case mainExp of
                    Nothing    -> S.empty
                    Just (e,_) -> collect_syms S.empty e) <>
                 (M.foldl (\acc fn -> collect_syms acc (funBody fn)) S.empty fundefs)


      collect_syms :: S.Set String -> Exp3 -> S.Set String
      collect_syms syms ex =
        let go  = collect_syms syms
            gol = foldl collect_syms syms in
        case ex of
          VarE{}    -> syms
          LitE{}    -> syms
          FloatE{}  -> syms
          LitSymE v -> S.insert (fromVar v) syms
          AppE _ _ args   -> gol args
          PrimAppE _ args -> gol args
          LetE (_,_,_,rhs) bod -> go rhs <> go bod
          IfE a b c  -> go a <> go b <> go c
          MkProdE ls -> gol ls
          ProjE _ e  -> go e
          CaseE scrt ls ->
            go scrt <> foldl (\acc (_,_,c) -> collect_syms acc c) syms ls
          DataConE _ _ ls -> gol ls
          TimeIt e _ _   -> go e
          WithArenaE _ e -> go e
          SpawnE _ _ ls  -> gol ls
          SyncE -> S.empty
          Ext ext        ->
            case ext of
              WriteScalar _ _ ex -> go ex
              AddCursor _ ex   -> go ex
              SubPtr{}         -> syms
              WriteCursor _ ex -> go ex
              ReadScalar{}   -> syms
              ReadTag{}      -> syms
              WriteTag{}     -> syms
              ReadList{}     -> syms
              WriteList _ ex _ -> go ex
              NewBuffer{}    -> syms
              ScopedBuffer{} -> syms
              InitSizeOfBuffer{} -> syms
              MMapFileSize{}     -> syms
              SizeOfPacked{}     -> syms
              SizeOfScalar{}     -> syms
              BoundsCheck{}      -> syms
              ReadCursor{}       -> syms
              BumpRefCount{}     -> syms
              NullCursor         -> syms
              BumpArenaRefCount{}-> error "collect_syms: BumpArenaRefCount not handled."
              RetE ls -> gol ls
              GetCilkWorkerNum -> syms
              LetAvail _ bod   -> collect_syms syms bod
          MapE{}         -> syms
          FoldE{}        -> syms


  tail :: M.Map String Word16 -> Exp3 -> PassM T.Tail
  tail sym_tbl ex0 = do
   dflags <- getDynFlags
   let pkd = gopt Opt_Packed dflags
   case ex0 of

    -- HACK! We don't have LetSwitchT yet.  This means potential exponential code duplication:
    -- LetE (_,_, CaseE _ _) _ ->
    --    error "lower: unfinished, we cannot let-bind the result of a switch yet."
    LetE (vr,_locs,ty, (CaseE scrt ls)) bod -> tail sym_tbl $
                                       dbgTrace 1 ("WARNING: Let-bound CasE, code duplication of this body:\n  "
                                                   ++sdoc bod)$
         -- For now just duplicate code:
         CaseE scrt [ (k,vs, mkLet (vr,ty,e) bod)
                    | (k,vs,e) <- ls]

    -- Aaand... if we're going to push Let's under Case's, we have to repeat this bit of flattening:
    LetE (v1, locs, t1, (LetE (v2,locs2,t2,rhs2) rhs1)) bod ->
       tail sym_tbl $ LetE (v2,locs,t2,rhs2) $ LetE (v1,locs2,t1,rhs1) bod

    --------------------------------------------------------------------------------
    -- Packed codegen
    --------------------------------------------------------------------------------

    -- Likewise, Case really means ReadTag.  Argument is a cursor.
    CaseE (VarE scrut) ls | pkd -> do
        tagtmp <- gensym $ toVar "tmpval"
        ctmp   <- gensym $ toVar "tmpcur"
        -- Here we lamely chase down all the tuple references and make them variables:
        -- So that Goto's work properly (See [Modifying switch statements to use redirection nodes]).
        let doalt (k,ls,rhs) = do
              let rhs' = L3.substE (Ext (AddCursor scrut (LitE 1))) (VarE ctmp) $
                         rhs
              -- We only need to thread one value through, the cursor resulting from read.
              (getTagOfDataCon ddefs k,) <$>
                case ls of
                  []  -> tail sym_tbl rhs' -- AUDITME -- is this legit, or should it have one cursor param anyway?
                  [(c,_)] -> tail sym_tbl (subst c (VarE ctmp) rhs')
                  oth -> error $ "lower.tail.CaseE: unexpected pattern" ++ show oth
        alts <- mapM doalt ls
        let def_alt = T.ErrT $ "Unknown tag in: " ++ fromVar tagtmp
        lbl <- gensym "switch"
        return $
         T.LetPrimCallT [(tagtmp,T.TagTyPacked),(ctmp,T.CursorTy)] T.ReadTag [T.VarTriv scrut] $
          T.Switch lbl
                   (T.VarTriv tagtmp)
                   (T.TagAlts alts)
                   (Just def_alt)

    --------------------------------------------------------------------------------
    -- Not-packed, pointer-based codegen
    --------------------------------------------------------------------------------
    -- In pointer-based representation we don't use `TagTyPacked`, because it is
    -- causing problems.  By default gcc aligns struct fields but we don't
    -- take that padding into account in our codegen.
    --
    -- If we get here that means we're NOT packing trees on this run:
    -- Thus this operates on BOXED data:
    CaseE e [(c, bndrs, rhs)] | not pkd -> do
      -- a product, directly assign the fields
      let tys = L.map typ (lookupDataCon ddefs c)
          (bndrs2,_) = unzip bndrs

      -- TODO(osa): enable this
      -- ASSERT(length tys == length bndrs)

      let T.VarTriv e_var = triv sym_tbl "product case scrutinee" e
      tag_bndr  <- gensym $ toVar "tag"

      let bndrs' = tag_bndr : bndrs2
          tys'   = T.IntTy  : tys
      rhs' <- tail sym_tbl rhs
      return (T.LetUnpackT (zip bndrs' tys') e_var rhs')

    CaseE e alts | not pkd -> do
      tag_bndr <- gensym $ toVar "tag"
      tail_bndr <- gensym $ toVar "tail"

      let
        e_triv = triv sym_tbl "sum case scrutinee" e

        mk_alt :: (DataCon, [(Var,())], Exp3) -> PassM (Int64, T.Tail)
        mk_alt (con, bndrs, rhs) = do
          let
            con_tag = getTagOfDataCon ddefs con
            bndr_tys = L.map typ (lookupDataCon ddefs con)
            (bndrs',_) = unzip bndrs
          rhs' <- tail sym_tbl rhs
          return ( fromIntegral con_tag, T.LetUnpackT (zip bndrs' bndr_tys) tail_bndr rhs' )

      alts' <- mapM mk_alt alts
      let def_alt = T.ErrT $ "Unknown tag in: " ++ fromVar tag_bndr
      lbl <- gensym "switch"

      return $
        T.LetPrimCallT
          [(tag_bndr, T.TagTyPacked), (tail_bndr, T.CursorTy)]
          (T.ReadScalar IntS)
          [e_triv]
          (T.Switch lbl (T.VarTriv tag_bndr) (T.IntAlts alts') (Just def_alt))


    -- Accordingly, constructor allocation becomes an allocation.
    LetE (v, _, _, (DataConE _ k ls)) bod | not pkd -> L3.assertTrivs ls $ do
      let tycon    = getTyOfDataCon ddefs k
          all_cons = dataCons (lookupDDef ddefs tycon)
          tag      = fromJust (L.findIndex ((==) k . fst) all_cons)

          field_tys= L.map typ (lookupDataCon ddefs k)
          fields0  = fragileZip field_tys (L.map (triv sym_tbl "DataConE args") ls)
          fields   = (T.IntTy, T.IntTriv (fromIntegral tag)) : fields0
          --  | is_prod   = fields0
          --  | otherwise = (T.IntTy, T.IntTriv (fromIntegral tag)) : fields0
      bod' <- tail sym_tbl bod
      return (T.LetAllocT v fields bod')


    -- This is legitimately flattened, but we need to move it off the spine:
    DataConE _ k _ls -> do
       tmp <- gensym $ toVar "tailift"
       let ty = L3.PackedTy (getTyOfDataCon ddefs k) ()
       tail sym_tbl $ LetE (tmp, [], ty, ex0) (VarE tmp)

    --------------------------------------------------------------------------------

    -- Ext (RetE ls)   -> pure$ T.RetValsT (L.map (triv sym_tbl "returned element of tuple") ls)
    --
    MkProdE ls      -> pure$ T.RetValsT (L.map (triv sym_tbl "returned element of tuple") ls)
    e | isTrivial e -> pure$ T.RetValsT [triv sym_tbl "<internal error1>" (e)]

    -- We could eliminate these ahead of time (unariser):
    -- FIXME: Remove this when that is done a priori:
    LetE (v, _, ProdTy tys, (MkProdE ls)) bod -> do
      (tmps,bod') <- eliminateProjs v tys bod
      let bod'' = updateAvailVars [v] tmps bod'
      -- Bind tmps individually:a
      let go [] acc                 = acc
          go ((pvr,pty,rhs):rs) acc = go rs (LetE (pvr,[],pty,rhs) acc)
      -- Finally reprocess the whole thing
      tail sym_tbl (go (zip3 tmps tys ls) bod'')

    LetE (v, _, ty, rhs@(ProjE{})) bod -> do
      let trv = triv sym_tbl "ProjE" rhs
      bod' <- tail sym_tbl bod
      pure $ T.LetTrivT (v,typ ty,trv) bod'

    WithArenaE v e -> do
      e' <- tail sym_tbl e
      return $ T.LetArenaT v e'

    -- We could eliminate these ahead of time:
    LetE (v,_,t,rhs) bod | isTrivial' rhs ->
      T.LetTrivT (v,typ t, triv sym_tbl "<internal error2>" rhs) <$> tail sym_tbl bod

    IfE a b c -> do b' <- tail sym_tbl b
                    c' <- tail sym_tbl c
                    return $ T.IfT (triv sym_tbl "if test" a) b' c'

    LetE (vr, _, ty, (L3.TimeIt rhs _ flg)) bod ->
        do rhs' <- tail sym_tbl rhs
           case ty of
             ProdTy ls ->
               do (tmps,bod') <- eliminateProjs vr ls bod
                  let bod'' = updateAvailVars [vr] tmps bod'
                  T.LetTimedT flg (zip tmps (L.map typ ls)) rhs' <$> tail sym_tbl bod''
             _ -> T.LetTimedT flg   [(vr, typ ty)]          rhs' <$> tail sym_tbl bod


    --------------------------------Start PrimApps----------------------------------
    -- (1) Primapps that become Tails:

    -- FIXME: No reason errors can't stay primitive at Target:
    PrimAppE (ErrorP str _ty) [] ->
      pure $ T.ErrT str

    LetE (_,_,_, (PrimAppE (L3.ErrorP str _) [])) _ ->
      pure $ T.ErrT str

    -- Whatever... a little just-in-time flattening.  Should obsolete this:
    PrimAppE (DictEmptyP ty) ((VarE v):ls) -> do
      tmp <- gensym $ toVar "flt"
      tail sym_tbl (LetE (tmp, [], SymDictTy (Just v) ty, PrimAppE (DictEmptyP ty) ((VarE v):ls)) (VarE tmp))

    PrimAppE (DictInsertP ty) ((VarE v):ls) -> do
      tmp <- gensym $ toVar "flt"
      tail sym_tbl (LetE (tmp, [], SymDictTy (Just v) ty, PrimAppE (DictInsertP ty) ((VarE v):ls)) (VarE tmp))

    PrimAppE p ls -> do
      tmp <- gensym $ toVar "flt"
      tail sym_tbl (LetE (tmp, [], primRetTy p, PrimAppE p ls) (VarE tmp))

    ---------------------
    -- (2) Next FAKE Primapps.  These could be added to L3 if we wanted to pollute it.

    LetE (v,_,_,  (Ext (ReadScalar s cur))) bod -> do
      vtmp <- gensym $ toVar "tmpval"
      ctmp <- gensym $ toVar "tmpcur"

      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L3.substE (ProjE 0 (VarE v)) (VarE vtmp) $
                 L3.substE (ProjE 1 (VarE v)) (VarE ctmp)
                 bod

      dbgTrace 7 (" [lower] ReadInt, after substing references to "
                  ++(fromVar v)++":\n  "++sdoc bod') <$>
        T.LetPrimCallT [(vtmp, T.scalarToTy s),(ctmp,T.CursorTy)] (T.ReadScalar s) [T.VarTriv cur] <$>
          tail sym_tbl bod'

    LetE (v, _, _,  (Ext (WriteScalar s c e))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] (T.WriteScalar s) [triv sym_tbl "WriteTag arg" e, T.VarTriv c] <$>
         tail sym_tbl bod


    -- In Target, AddP is overloaded still:
    LetE (v,_, _,  (Ext (AddCursor c ( (Ext (InitSizeOfBuffer mul)))))) bod -> do
      size <- gensym (varAppend "sizeof_" v)
      T.LetPrimCallT [(size,T.IntTy)] (T.InitSizeOfBuffer mul) [] <$>
        T.LetPrimCallT [(v,T.CursorTy)] T.AddP [ triv sym_tbl "addCursor base" (VarE c)
                                               , triv sym_tbl "addCursor offset" (VarE size)] <$>
        tail sym_tbl bod

    LetE (v,_, _,  (Ext (AddCursor c ( (Ext (MMapFileSize w)))))) bod -> do
      size <- gensym (varAppend "sizeof_" v)
      T.LetPrimCallT [(size,T.IntTy)] (T.MMapFileSize w) [] <$>
        T.LetPrimCallT [(v,T.CursorTy)] T.AddP [ triv sym_tbl "addCursor base" (VarE c)
                                               , triv sym_tbl "addCursor offset" (VarE size)] <$>
        tail sym_tbl bod

    LetE (v,_, _,  (Ext (AddCursor c e))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] T.AddP [ triv sym_tbl "addCursor base" (VarE c)
                                             , triv sym_tbl "addCursor offset" e] <$>
         tail sym_tbl bod

    LetE (v,_, _,  (Ext (SubPtr a b))) bod ->
      T.LetPrimCallT [(v,T.IntTy)] T.SubP [ triv sym_tbl "subCursor base" (VarE a)
                                          , triv sym_tbl "subCursor offset" (VarE b)] <$>
         tail sym_tbl bod

    LetE (v,_, _,  (Ext (ReadTag cur))) bod -> do
      vtmp <- gensym $ toVar "tmptag"
      ctmp <- gensym $ toVar "tmpcur"

      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L3.substE (ProjE 0 (VarE v)) (VarE vtmp) $
                 L3.substE (ProjE 1 (VarE v)) (VarE ctmp)
                 bod

      dbgTrace 7 (" [lower] ReadTag, after substing references to "
                  ++(fromVar v)++":\n  "++sdoc bod') <$>
        T.LetPrimCallT [(vtmp,T.TagTyPacked),(ctmp,T.CursorTy)] T.ReadTag [T.VarTriv cur] <$>
          tail sym_tbl bod'
      -- error $ "lower: ReadTag not handled yet."


    LetE (cursOut,_, _,  (Ext (WriteTag dcon cursIn))) bod -> do
      T.LetPrimCallT [(cursOut,T.CursorTy)] T.WriteTag
        [ T.TagTriv (getTagOfDataCon ddefs dcon) , triv sym_tbl "WriteTag cursor" (VarE cursIn) ] <$>
        tail sym_tbl bod

    LetE (v,_,_,  (Ext (NewBuffer mul))) bod -> do
      reg <- gensym "region"
      tl' <- T.LetPrimCallT [(reg,T.CursorTy),(v,T.CursorTy)] (T.NewBuffer mul) [] <$>
               tail sym_tbl bod
      -- The type shouldn't matter. PtrTy is not used often in current programs,
      -- and would be easy to spot.
      T.withTail (tl',T.PtrTy) $ \trvs ->
         (T.LetPrimCallT [] T.FreeBuffer [(T.VarTriv reg),(T.VarTriv v),(T.VarTriv (toEndV v))] $
            T.RetValsT trvs)

    LetE (v,_,_,  (Ext (ScopedBuffer mul))) bod -> do
      T.LetPrimCallT [(v,T.CursorTy)] (T.ScopedBuffer mul) [] <$>
         tail sym_tbl bod

    LetE (v,_,_,  (Ext (SizeOfPacked start end))) bod -> do
      T.LetPrimCallT [(v,T.IntTy)] T.SizeOfPacked [ T.VarTriv start, T.VarTriv end ] <$>
        tail sym_tbl bod

    LetE (v,_,_,  (Ext (SizeOfScalar w))) bod -> do
      T.LetPrimCallT [(v,T.IntTy)] T.SizeOfScalar [ T.VarTriv w ] <$>
        tail sym_tbl bod

    -- Just a side effect
    LetE(_,_,_,  (Ext (BoundsCheck i bound cur))) bod -> do
      let args = [T.IntTriv (fromIntegral i), T.VarTriv bound, T.VarTriv cur]
      T.LetPrimCallT [] T.BoundsCheck args <$> tail sym_tbl bod

    LetE(v,_,_,  (Ext (ReadCursor c))) bod -> do
      vtmp <- gensym $ toVar "tmpcur"
      ctmp <- gensym $ toVar "tmpaftercur"
      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L3.substE (ProjE 0 (VarE v)) (VarE vtmp) $
                 L3.substE (ProjE 1 (VarE v)) (VarE ctmp)
                 bod
      T.LetPrimCallT [(vtmp,T.CursorTy),(ctmp,T.CursorTy)] T.ReadCursor [T.VarTriv c] <$>
        tail sym_tbl bod'

    LetE(v,_,_,  (Ext (ReadList c el_ty))) bod -> do
      vtmp <- gensym $ toVar "tmplist"
      ctmp <- gensym $ toVar "tmpafterlist"
      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L3.substE (ProjE 0 (VarE v)) (VarE vtmp) $
                 L3.substE (ProjE 1 (VarE v)) (VarE ctmp)
                 bod
      T.LetPrimCallT [(vtmp,T.VectorTy (T.fromL3Ty el_ty)),(ctmp,T.CursorTy)] T.ReadList [T.VarTriv c] <$>
        tail sym_tbl bod'

    LetE (v, _, _,  (Ext (WriteList cur e _el_ty))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] T.WriteList [triv sym_tbl "WriteList arg" e, T.VarTriv cur] <$>
         tail sym_tbl bod

    LetE (v, _, _,  (Ext (WriteCursor cur e))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] T.WriteCursor [triv sym_tbl "WriteCursor arg" e, T.VarTriv cur] <$>
         tail sym_tbl bod

    LetE (_, _, _,  (Ext (BumpRefCount end_r1 end_r2))) bod ->
      T.LetPrimCallT [] T.BumpRefCount [T.VarTriv end_r1, T.VarTriv end_r2] <$>
        tail sym_tbl bod

    LetE (_, _, _,  (Ext (BumpArenaRefCount ar end_r))) bod ->
      T.LetPrimCallT [] T.BumpArenaRefCount [T.VarTriv ar, T.VarTriv end_r] <$>
        tail sym_tbl bod

    LetE (v, _, _,  (Ext NullCursor)) bod ->
      T.LetTrivT (v,T.CursorTy,T.IntTriv 0) <$> tail sym_tbl bod

    LetE (v, _, ty, (Ext GetCilkWorkerNum)) bod ->
      T.LetPrimCallT [(v,typ ty)] T.GetCilkWorkerNum [] <$> tail sym_tbl bod

    Ext (LetAvail vs bod) ->
      T.LetAvailT vs <$> tail sym_tbl bod

    Ext _ -> error $ "lower: unexpected extension" ++ sdoc ex0

    ---------------------
    -- (3) Proper primapps.
    LetE (v,_,t,  (PrimAppE p ls)) bod -> dbgTrace 7 ("lower: " ++ show v ++ " : " ++ show t) $
        -- No tuple-valued prims here:
        T.LetPrimCallT [(v,typ t)]
             (prim p)
             (L.map (triv sym_tbl $ "prim rand "++show p) ls) <$>
             (tail sym_tbl bod)
    --------------------------------End PrimApps----------------------------------

    AppE v _ ls -> return $ T.TailCall v (map (triv sym_tbl "operand") ls)

    SpawnE{} -> error "lower: Unbound SpanwnE"
    SyncE    -> error "lower: Unbound SpanwnE"

    -- Tail calls are just an optimization, if we have a Proj/App it cannot be tail:
    ProjE ix ( (AppE f _ e)) -> dbgTrace 5 "ProjE" $ do
        tmp <- gensym $ toVar "prjapp"
        let (inTs, _) = funTy (fundefs # f)
        tail sym_tbl $
          LetE ( tmp
                  , []
                  , fmap (const ()) (inTs !! ix)
                  , ProjE ix (AppE f [] e))
             (VarE tmp)

    LetE (_,_,_, ( (L3.AppE f _ _))) _
        | M.notMember f fundefs -> error $ "Application of unbound function: "++show f

    -- Non-tail call:
    LetE (vr, _,t, projOf -> (stk, ( (L3.AppE f _ ls)))) bod -> do
        let (_ , outTy) = funTy (fundefs # f)
        let f' = cleanFunName f
        (vsts,bod') <- case outTy of
                        L3.ProdTy [] -> error "lower: FINISHME: unit valued function"
                        L3.ProdTy tys ->
                          case stk of
                            [] -> do (tmps,e) <- eliminateProjs vr (L.map (fmap (const ())) tys) bod
                                     let e' = updateAvailVars [vr] tmps e
                                     return (zip tmps (L.map typ tys), e')
                            -- More than one should not currently be
                            -- possible (no nested tuple returns):
                            [ix] -> do garbages <- sequence [ gensym "garbage" | _ <- L.tail tys ]
                                       let (lead,trail) = L.splitAt ix garbages
                                       return ( zip (lead++[vr]++trail)
                                                    (L.map typ tys)
                                              , bod)
                            oth -> error $ "lower.tail.LetE: unexpected pattern" ++ show oth
                        _ -> return ([(vr,typ t)], bod)
        T.LetCallT False vsts f' (L.map (triv sym_tbl "one of app rands") ls) <$> (tail sym_tbl bod')

    LetE (v, _,ty, L3.SpawnE fn locs args) bod -> do
      tl <- tail sym_tbl (LetE (v,_,ty, AppE fn locs args) bod)
      -- This is going to be a LetCallT.
      pure $ tl { T.async = True }

    LetE (_,_,_,  SyncE) bod -> do
      bod' <- tail sym_tbl bod
      pure $ T.LetPrimCallT [] T.ParSync [] bod'

    LetE (v, _, t,  (IfE a b c)) bod -> do
      let a' = triv sym_tbl "if test" a
      b' <- tail sym_tbl b
      c' <- tail sym_tbl c
      case t of
        -- Finilize unarisation:
        ProdTy ls -> do
             (tmps,bod') <- eliminateProjs v ls bod
             let bod'' = updateAvailVars [v] tmps bod'
             T.LetIfT (zip tmps (L.map typ ls)) (a', b', c') <$> tail sym_tbl bod''
        _ -> T.LetIfT [(v, typ t)] (a', b', c') <$> tail sym_tbl bod


    _ -> error$ "lower: unexpected expression in tail position:\n  "++sdoc ex0


-- Helpers
--------------------------------------------------------------------------------

-- | View pattern for matching agaist projections of Foo rather than just Foo.
projOf :: Exp3 -> ([Int], Exp3)
projOf ( (ProjE ix e)) = let (stk,e') = projOf e
                           in (stk++[ix], e')
projOf e = ([],e)



-- | Eliminate projections from a given tuple variable.  INEFFICIENT!
eliminateProjs :: Var -> [Ty3] -> Exp3 -> PassM ([Var],Exp3)
eliminateProjs vr tys bod =
 dbgTrace 7 (" [lower] eliminating "++show (length tys)++
             " projections on variable "++show vr++" in expr with types "
                                        ++show tys++":\n   "++sdoc bod) $
 do tmps <- mapM (\_ -> gensym "pvrtmp") [1.. (length tys)]
    let go _ [] acc =
            -- If there are ANY references left, we are forced to make the products:
            L3.subst vr (MkProdE (L.map VarE tmps)) acc
        go ix ((pvr,_pty):rs) acc =
           go (ix+1) rs
             (L3.substE (ProjE ix (VarE vr)) (VarE pvr) acc)
    let bod' = go 0 (zip tmps tys) bod
    return (tmps,bod')



mkLet :: (Var, Ty3, Exp3) -> Exp3 -> Exp3
mkLet (v,t,  (LetE (v2, _,t2,rhs2) bod1)) bod2 = LetE (v2,[],t2,rhs2) $
                                                    LetE (v,[],t,bod1) bod2
mkLet (v,t,rhs) bod = LetE (v,[],t,rhs) bod



triv :: M.Map String Word16 -> String -> Exp3 -> T.Triv
triv sym_tbl msg ( e0) =
  case e0 of
    (VarE x) -> T.VarTriv x
    (LitE x) -> T.IntTriv (fromIntegral x)      -- TODO: back propogate Int64 to L1
    (FloatE x)  -> T.FloatTriv x -- TODO: back propogate Int64 to L1
    (LitSymE v) -> let s = fromVar v in
                   case M.lookup s sym_tbl of
                     Just i  -> T.SymTriv i
                     -- Impossible case, b/c we collect all the symbols in the
                     -- program in the very first step.
                     Nothing -> error $ "triv: Symbol not found in table: " ++ sdoc s
    -- Bools become ints:
    (PrimAppE L3.MkTrue [])  -> T.IntTriv 1
    (PrimAppE L3.MkFalse []) -> T.IntTriv 0
    -- Heck, let's map Unit onto Int too:
    (MkProdE []) -> T.IntTriv 0
    (MkProdE ls) -> T.ProdTriv (map (\x -> triv sym_tbl (show x) x) ls)
    (ProjE ix e) -> T.ProjTriv ix (triv sym_tbl "proje argument" e)
    _ | isTrivial e0 -> error $ "lower/triv: this function is written wrong.  "++
                         "It won't handle the following, which satisfies 'isTriv':\n "++sdoc e0++
                         "\nMessage: "++msg
    _ -> error $ "lower/triv, expected trivial in "++msg++", got "++sdoc e0

typ :: UrTy () -> T.Ty
typ t =
  case t of
    IntTy  -> T.IntTy
    FloatTy-> T.FloatTy
    SymTy  -> T.SymTy
    BoolTy -> T.BoolTy
    VectorTy el_ty -> T.VectorTy (typ el_ty)
    ProdTy xs -> T.ProdTy $ L.map typ xs
    SymDictTy (Just var) x -> T.SymDictTy var $ typ x
    SymDictTy Nothing _ty -> error $ "lower/typ: Expected arena annotation on type: " ++ (sdoc t)
    -- t | isCursorTy t -> T.CursorTy
    PackedTy{} -> T.PtrTy
    CursorTy -> T.CursorTy -- Audit me
    PtrTy -> T.PtrTy
    ArenaTy   -> T.ArenaTy
    SymSetTy  -> error "lower/typ: SymSetTy not handled."
    SymHashTy -> error "lower/typ: SymHashTy not handled."

typ' :: String -> Ty3 -> T.Ty
typ' str t = dbgTraceIt str $ typ t

prim :: Prim Ty3 -> T.Prim
prim p =
  case p of
    AddP -> T.AddP
    SubP -> T.SubP
    MulP -> T.MulP
    DivP -> T.DivP
    ModP -> T.ModP
    ExpP -> T.ExpP
    FAddP -> T.AddP
    FSubP -> T.SubP
    FMulP -> T.MulP
    FDivP -> T.DivP
    FExpP -> T.ExpP
    FRandP-> T.FRandP
    FSqrtP-> T.FSqrtP
    FloatToIntP -> T.FloatToIntP
    IntToFloatP -> T.IntToFloatP
    RandP -> T.RandP
    Gensym -> T.Gensym
    EqSymP -> T.EqP
    EqIntP -> T.EqP
    EqFloatP -> T.EqP
    LtP    -> T.LtP
    GtP    -> T.GtP
    LtEqP  -> T.LtEqP
    GtEqP  -> T.GtEqP
    FLtP   -> T.LtP
    FGtP   -> T.GtP
    FLtEqP -> T.LtEqP
    FGtEqP -> T.GtEqP
    OrP    -> T.OrP
    AndP   -> T.AndP
    SizeParam -> T.SizeParam
    IsBig    -> T.IsBig
    PrintInt -> T.PrintInt
    PrintSym -> T.PrintSym
    ReadInt  -> T.ReadInt
    DictInsertP ty -> T.DictInsertP $ typ ty
    DictLookupP ty -> T.DictLookupP $ typ ty
    DictEmptyP ty  -> T.DictEmptyP $ typ ty
    DictHasKeyP ty -> T.DictHasKeyP $ typ ty
    ReadPackedFile mf tyc _ _ -> T.ReadPackedFile mf tyc
    ReadArrayFile fp ty -> T.ReadArrayFile fp (typ ty)
    VEmptyP ty    -> T.VEmptyP (typ ty)
    VNthP ty      -> T.VNthP (typ ty)
    VLengthP ty   -> T.VLengthP (typ ty)
    VUpdateP ty   -> T.VUpdateP (typ ty)
    VSnocP ty     -> T.VSnocP (typ ty)
    VSortP ty     -> T.VSortP (typ ty)
    InPlaceVSnocP ty -> T.InPlaceVSnocP (typ ty)
    InPlaceVSortP ty -> T.InPlaceVSortP (typ ty)
    VSliceP ty    -> T.VSliceP (typ ty)
    SymSetEmpty   -> error "lower/prim: SymSetEmpty not handled"
    SymSetInsert  -> error "lower/prim: SymSetInsert not handled"
    SymSetContains-> error "lower/prim: SymSetContains not handled"
    SymHashEmpty  -> error "lower/prim: SymHashEmpty not handled"
    SymHashInsert  -> error "lower/prim: SymHashInsert not handled"
    SymHashLookup  -> error "lower/prim: SymHashLookup not handled"
    IntHashEmpty  -> error "lower/prim: IntHashEmpty not handled"
    IntHashInsert  -> error "lower/prim: IntHashInsert not handled"
    IntHashLookup  -> error "lower/prim: IntHashLookup not handled"

    ErrorP{}     -> error$ "lower/prim: internal error, should not have got to here: "++show p
    MkTrue       -> error "lower/prim: internal error. MkTrue should not get here."
    MkFalse      -> error "lower/prim: internal error. MkFalse should not get here."
    SymAppend    -> error "lower/prim: internal error. SymAppend should not get here."
    RequestEndOf -> error "lower/prim: internal error. RequestEndOf shouldn't be here."
    RequestSizeOf -> error "lower/prim: internal error. RequestSizeOf shouldn't be here."

isTrivial' :: Exp3 -> Bool
isTrivial' e =
    case e of
      (PrimAppE L3.MkTrue []) -> True
      (PrimAppE L3.MkFalse []) -> True
      _ -> isTrivial e
