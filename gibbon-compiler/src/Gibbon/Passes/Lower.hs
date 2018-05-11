{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}


-------------------------------------------------------------------------------

-- | Lowering L1 to the target language.
module Gibbon.Passes.Lower
  ( lower
  ) where

-------------------------------------------------------------------------------

import Control.Monad
import Data.Char
import Data.Maybe
import Data.Loc
import Data.List as L hiding (tail)
import Data.Map as M hiding (foldl, foldr)
import Data.Int (Int64)
import Prelude hiding (tail)
import qualified Data.List as L
-- import Data.Word


import Gibbon.GenericOps
import Gibbon.Common hiding (FunDef)
import Gibbon.L1.Syntax hiding (FunDef, Prog(..), progToEnv)
import Gibbon.L3.Syntax
import qualified Gibbon.L1.Syntax as L1
import qualified Gibbon.L4.Syntax as T
-- import           Gibbon.L1.Syntax (Exp(..))
-- import qualified Gibbon.L2.Syntax as L2
-- import           Gibbon.L2.Syntax ( FunDef(..), Prog(..) )


-- Generating unpack functions from Packed->Pointer representation:
-------------------------------------------------------------------------------

genDcons :: [Ty3] -> Var -> [(T.Ty, T.Triv)] -> SyM T.Tail
genDcons (x:xs) tail fields = case x of
  IntTy             ->  do
    val  <- gensym "val"
    t    <- gensym "tail"
    T.LetPrimCallT [(val, T.IntTy), (t, T.CursorTy)] T.ReadInt [(T.VarTriv tail)]
      <$> genDcons xs t (fields ++ [(T.IntTy, T.VarTriv val)])

  PackedTy tyCons _ -> do
    ptr  <- gensym  "ptr"
    t    <- gensym  "tail"
    T.LetCallT [(ptr, T.PtrTy), (t, T.CursorTy)] (mkUnpackerName tyCons) [(T.VarTriv tail)]
      <$> genDcons xs t (fields ++ [(T.CursorTy, T.VarTriv ptr)])

  -- Indirection, don't do anything
  CursorTy -> do
    next <- gensym "next"
    afternext <- gensym "afternext"
    T.LetPrimCallT [(next, T.CursorTy),(afternext,T.CursorTy)] T.ReadCursor [(T.VarTriv tail)] <$>
      genDcons xs afternext fields

  _ -> error $ "genDcons: FIXME " ++ show x

genDcons [] tail fields     = do
  ptr <- gensym "ptr"
  return $ T.LetAllocT ptr fields $ T.RetValsT [T.VarTriv ptr, T.VarTriv tail]

genAlts :: [(DataCon,[(IsBoxed,Ty3)])] -> Var -> Var -> Int64 -> SyM T.Alts
genAlts ((dcons, typs):xs) tail tag n = do
  let (_,typs') = unzip typs
  -- WARNING: IsBoxed ignored here
  curTail <- genDcons typs' tail [(T.TagTyPacked, T.VarTriv tag)]
  alts    <- genAlts xs tail tag (n+1)
  let alt = if isIndirectionTag dcons
            then indirectionAlt
            else n
  case alts of
    T.IntAlts []   -> return $ T.IntAlts [(alt::Int64, curTail)]
    -- T.TagAlts []   -> return $ T.TagAlts [(n::Word8, curTail)]
    T.IntAlts tags -> return $ T.IntAlts ((alt::Int64, curTail) : tags)
    -- T.TagAlts tags -> return $ T.TagAlts ((n::Word8, curTail) : tags)
    _              -> error $ "Invalid case statement type."

genAlts [] _ _ _                  = return $ T.IntAlts []

genUnpacker :: DDef Ty3 -> SyM T.FunDecl
genUnpacker DDef{tyName, dataCons} = do
  p    <- gensym "p"
  tag  <- gensym "tag"
  tail <- gensym "tail"
  alts <- genAlts dataCons tail tag 0
  lbl  <- gensym "switch"
  bod  <- return $ T.LetPrimCallT [(tag, T.TagTyPacked), (tail, T.CursorTy)] T.ReadTag [(T.VarTriv p)] $
            T.Switch lbl (T.VarTriv tag) alts Nothing
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
genDconsPrinter :: [Ty3] -> Var -> SyM T.Tail
genDconsPrinter (x:xs) tail = case x of
  L1.IntTy             ->  do
    val  <- gensym "val"
    t    <- gensym "tail"
    T.LetPrimCallT [(val, T.IntTy), (t, T.CursorTy)] T.ReadInt [(T.VarTriv tail)] <$>
      printTy False L1.IntTy [T.VarTriv val] <$>
       maybeSpace <$>
        genDconsPrinter xs t

  L1.PackedTy tyCons _ -> do
    val  <- gensym "val"
    t    <- gensym "tail"
    tmp  <- gensym "temp"
    valc <- gensym "valcur"
    T.LetPrimCallT [(val, T.IntTy), (t, T.CursorTy)] T.ReadInt [(T.VarTriv tail)] <$>
      T.LetTrivT (valc, T.CursorTy, T.VarTriv val) <$>
      T.LetCallT [(tmp, T.PtrTy)] (mkPrinterName tyCons) [(T.VarTriv valc)] <$>
       maybeSpace <$>
         genDconsPrinter xs t

  L1.CursorTy -> genDconsPrinter xs tail

  _ -> error "FINISHME: genDconsPrinter"

 where
  maybeSpace = if L.null xs
               then id
               else printSpace

genDconsPrinter [] tail     = do
  return $ closeParen $ T.RetValsT [(T.VarTriv tail)]

genAltPrinter :: [(DataCon,[(IsBoxed, Ty3)])] -> Var -> Int64 -> SyM T.Alts
genAltPrinter ((dcons, typs):xs) tail n = do
  let (_,typs') = unzip typs
  -- WARNING: IsBoxed ignored here
  curTail <- (openParen dcons) <$> genDconsPrinter typs' tail
  alts    <- genAltPrinter xs tail (n+1)
  let alt = if isIndirectionTag dcons
            then indirectionAlt
            else n
  case alts of
    T.IntAlts []   -> return $ T.IntAlts [(alt::Int64, curTail)]
    -- T.TagAlts []   -> return $ T.TagAlts [(n::Word8, curTail)]
    T.IntAlts tags -> return $ T.IntAlts ((alt::Int64, curTail) : tags)
    -- T.TagAlts tags -> return $ T.TagAlts ((n::Word8, curTail) : tags)
    _              -> error $ "Invalid case statement type."
genAltPrinter [] _ _                = return $ T.IntAlts []

genPrinter  :: DDef Ty3 -> SyM T.FunDecl
genPrinter DDef{tyName, dataCons} = do
  p    <- gensym "p"
  tag  <- gensym "tag"
  tail <- gensym "tail"
  alts <- genAltPrinter dataCons tail 0
  lbl  <- gensym "switch"
  -- TODO: Why is this ReadInt ?
  bod  <- return $ T.LetPrimCallT [(tag, T.TagTyPacked), (tail, T.CursorTy)] T.ReadInt [(T.VarTriv p)] $
            T.Switch lbl (T.VarTriv tag) alts Nothing
  return T.FunDecl{ T.funName  = mkPrinterName (fromVar tyName),
                    T.funArgs  = [(p, T.CursorTy)],
                    T.funRetTy = T.PtrTy,
                    T.funBody  = bod,
                    T.isPure   = False
                  }

printTy :: Bool -> Ty3 -> [T.Triv] -> (T.Tail -> T.Tail)
printTy pkd ty trvs =
  case (ty, trvs) of
    (IntTy, [_one])             -> T.LetPrimCallT [] T.PrintInt trvs
    (SymDictTy ty', [_one])     -> sandwich (printTy pkd ty' trvs) "Dict"
    (PackedTy constr _, [one]) -> -- HACK: Using varAppend here was the simplest way to get
                                  -- unique names without using the SyM monad.
                                  -- ASSUMPTION: Argument (one) is always a variable reference.
                                  -- This is reasonable because the AST is always flattened before
                                  -- we try to lower it.
                                  -- But we should change this to use gensym anyways..
                                  let T.VarTriv v = one
                                      unpkd = varAppend "unpkd_" v
                                      ignre = varAppend "ignre_" v
                                  in
                                    if pkd
                                    then (\tl -> T.LetCallT [(unpkd, T.PtrTy), (ignre, T.CursorTy)]
                                                 (mkUnpackerName constr) trvs $
                                                 T.LetCallT [] (mkPrinterName constr) [T.VarTriv unpkd] tl)
                                    else T.LetCallT [] (mkPrinterName constr) trvs
    (ListTy ty', [_one])        -> sandwich (printTy pkd ty' trvs) "List"

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

-- printTy ty trvs = error $ "Invalid L1 data type; " ++ show ty ++ " " ++ show trvs

addPrintToTail :: Bool -> Ty3 -> T.Tail-> SyM T.Tail
addPrintToTail pkd ty tl0 =
  let ty' = if pkd
            then T.IntTy
            else T.fromL3Ty ty
  in
    T.withTail (tl0, ty') $ \ trvs ->
      printTy pkd ty (properTrivs pkd ty trvs) $
        -- Always print a trailing newline at the end of execution:
        T.LetPrimCallT [] (T.PrintString "\n") [] $
          T.RetValsT []  -- Void return after printing.

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
lower :: (Bool,Maybe Ty3) -> Prog -> SyM T.Prog
lower (pkd,_mMainTy) Prog{fundefs,ddefs,mainExp} = do
  mn <- case mainExp of
          Nothing    -> return Nothing
          Just (x,mty) -> (Just . T.PrintExp) <$> (addPrintToTail pkd mty =<< tail x)

  funs       <- mapM fund (M.elems fundefs)
  unpackers  <- mapM genUnpacker (M.elems ddefs)
  printers   <- mapM genPrinter (M.elems ddefs)
  T.Prog <$> pure (funs ++ unpackers ++ printers) <*> pure mn

--  T.Prog <$> mapM fund (M.elems fundefs) <*> pure mn

 where
  fund :: FunDef -> SyM T.FunDecl
  fund FunDef{funname,funty=(ArrowTy inty outty),funarg,funbod} = do
      (args,bod) <- case inty of
                      -- ASSUMPTION: no nested tuples after unariser:
                      ProdTy ls -> do let tys'  = L.map (fmap (const ())) ls
                                          tys'' = L.map typ ls
                                      (vs,e') <- eliminateProjs funarg tys' funbod
                                      return $
                                        dbgTrace 5 (" [lower] unzipping funarg "++show funarg++" to "++show vs) $
                                        (zip vs tys'', e')
                      _ -> return ([(funarg, typ inty)], funbod)
      tl <- tail bod
      return T.FunDecl{ T.funName = funname
                      , T.funArgs = args
                      , T.funRetTy = typ outty
                      , T.funBody = tl
                      , T.isPure  = ispure funbod
                      }

  -- TimeIt forms are impure because they have print statements after codegen
  ispure :: L Exp3 -> Bool
  ispure (L _ ex) =
    case ex of
      TimeIt{} -> False
      LetE (_,_,_,rhs) bod -> ispure rhs && ispure bod
      IfE _ b c   -> ispure b && ispure c
      CaseE _ brs -> all id $ L.map (\(_,_,rhs) -> ispure rhs) brs
      _ -> True


  tail :: L Exp3 -> SyM T.Tail
  tail (L _ ex0) =
   dbgTrace 7 ("\n [lower] processing tail:\n  "++sdoc ex0) $
   case ex0 of

    -- HACK! We don't have LetSwitchT yet.  This means potential exponential code duplication:
    -- LetE (_,_, CaseE _ _) _ ->
    --    error "lower: unfinished, we cannot let-bind the result of a switch yet."
    LetE (vr,_locs,ty, L _ (CaseE scrt ls)) bod -> tail $
                                       dbgTrace 1 ("WARNING: Let-bound CasE, code duplication of this body:\n  "
                                                   ++sdoc bod)$
         -- For now just duplicate code:
         l$ CaseE scrt [ (k,vs, mkLet (vr,ty,e) bod)
                    | (k,vs,e) <- ls]

    -- Aaand... if we're going to push Let's under Case's, we have to repeat this bit of flattening:
    LetE (v1, locs, t1, L _ (LetE (v2,locs2,t2,rhs2) rhs1)) bod ->
       tail $ l$ LetE (v2,locs,t2,rhs2) $ l$ LetE (v1,locs2,t1,rhs1) bod

    --------------------------------------------------------------------------------
    -- Packed codegen
    --------------------------------------------------------------------------------

{-  We're directly generating WriteTag calls in the newer cursorize.
    But let's keep this around if we ever change that.

    -- These are in a funny normal form atfer cursor insertion.  They take one cursor arg.
    -- They basically are a WriteTag.
    LetE (cursOut, _, _, L _ (DataConE loc k ls)) bod | pkd -> do
      case ls of
       [cursIn] -> T.LetPrimCallT [(cursOut,T.CursorTy)] T.WriteTag
                     [ T.TagTriv (getTagOfDataCon ddefs k)
                     , triv "WriteTag cursor" cursIn ] <$>
                    tail bod
       _ -> error$ "Lower: Expected one argument to data-constructor (which becomes WriteTag): "
                   ++sdoc (DataConE loc k ls)

-}

    -- Likewise, Case really means ReadTag.  Argument is a cursor.
    CaseE (L _ (VarE scrut)) ls | pkd -> do
        let (last:restrev) = reverse ls
            rest = reverse restrev
        tagtmp <- gensym $ toVar "tmpval"
        ctmp   <- gensym $ toVar "tmpcur"
        -- Here we lamely chase down all the tuple references and make them variables:
        -- So that Goto's work properly (See [Modifying switch statements to use redirection nodes]).
        let doalt (k,ls,rhs) = do
              let rhs' = L1.substE (l$ Ext (AddCursor scrut (l$ LitE 1))) (l$ VarE ctmp) $
                         rhs
              -- We only need to thread one value through, the cursor resulting from read.
              (getTagOfDataCon ddefs k,) <$>
                case ls of
                  []  -> tail rhs' -- AUDITME -- is this legit, or should it have one cursor param anyway?
                  [(c,_)] -> tail (subst c (l$ VarE ctmp) rhs')
                  oth -> error $ "lower.tail.CaseE: unexpected pattern" ++ show oth
        alts <- mapM doalt rest
        (_,last') <- doalt last
        lbl <- gensym "switch"
        return $
         T.LetPrimCallT [(tagtmp,T.TagTyPacked),(ctmp,T.CursorTy)] T.ReadTag [T.VarTriv scrut] $
          T.Switch lbl
                   (T.VarTriv tagtmp)
                   (T.TagAlts alts)
                   (Just last')

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

      let T.VarTriv e_var = triv "product case scrutinee" e
      tag_bndr  <- gensym $ toVar "tag"

      let bndrs' = tag_bndr : bndrs2
          tys'   = T.IntTy  : tys
      rhs' <- tail rhs
      return (T.LetUnpackT (zip bndrs' tys') e_var rhs')

    CaseE e (def_alt : alts) | not pkd -> do
      tag_bndr <- gensym $ toVar "tag"
      tail_bndr <- gensym $ toVar "tail"

      let
        e_triv = triv "sum case scrutinee" e

        mk_alt :: (DataCon, [(Var,())], L Exp3) -> SyM (Int64, T.Tail)
        mk_alt (con, bndrs, rhs) = do
          let
            con_tag = getTagOfDataCon ddefs con
            bndr_tys = L.map typ (lookupDataCon ddefs con)
            (bndrs',_) = unzip bndrs
          rhs' <- tail rhs
          return ( fromIntegral con_tag, T.LetUnpackT (zip bndrs' bndr_tys) tail_bndr rhs' )

      alts'    <- mapM mk_alt alts
      (_, def) <- mk_alt def_alt
      lbl <- gensym "switch"

      return $
        T.LetPrimCallT
          [(tag_bndr, T.TagTyPacked), (tail_bndr, T.CursorTy)]
          T.ReadInt
          [e_triv]
          (T.Switch lbl (T.VarTriv tag_bndr) (T.IntAlts alts') (Just def))


    -- Accordingly, constructor allocation becomes an allocation.
    LetE (v, _, _, L _ (DataConE _ k ls)) bod | not pkd -> L1.assertTrivs ls $ do
      let tycon    = getTyOfDataCon ddefs k
          all_cons = dataCons (lookupDDef ddefs (toVar tycon))
          tag      = fromJust (L.findIndex ((==) k . fst) all_cons)

          field_tys= L.map typ (lookupDataCon ddefs k)
          fields0  = fragileZip field_tys (L.map (triv "DataConE args") ls)
          fields   = (T.IntTy, T.IntTriv (fromIntegral tag)) : fields0
          --  | is_prod   = fields0
          --  | otherwise = (T.IntTy, T.IntTriv (fromIntegral tag)) : fields0

      -- trace ("data con: " ++ show k) (return ())
      -- trace ("is_prod: " ++ show is_prod) (return ())
      -- trace ("fields: " ++ show fields) (return ())

      bod' <- tail bod

      return (T.LetAllocT v fields bod')


    -- This is legitimately flattened, but we need to move it off the spine:
    DataConE _ k _ls -> do
       tmp <- gensym $ toVar "tailift"
       let ty = L1.PackedTy (getTyOfDataCon ddefs k) ()
       tail $ l$ LetE (tmp, [], ty, l$ ex0) (l$ VarE tmp)

    --------------------------------------------------------------------------------

--    L1.LitE n       -> pure$ T.RetValsT [triv "literal in tail" (LitE n)]
    MkProdE ls   -> pure$ T.RetValsT (L.map (triv "returned element of tuple") ls)
    e | isTrivial e -> pure$ T.RetValsT [triv "<internal error1>" (l$ e)]


    -- Was already commented out in the old version.
    --
    -- L1.LetE (v,t, L1.MkProdE ls) bod -> do
    --   let rhss = L.map triv ls
    --   vsts <- unzipTup v t
    --   let go _ [] = tail bod
    --       go ix ((v1,t1):rst) = T.LetTrivT (v1,t1, )

    -- We could eliminate these ahead of time (unariser):
    -- FIXME: Remove this when that is done a priori:
    LetE (v, _, ProdTy tys, L _ (MkProdE ls)) bod -> do
      (tmps,bod') <- eliminateProjs v tys bod
      -- Bind tmps individually:a
      let go [] acc                 = acc
          go ((pvr,pty,rhs):rs) acc = go rs (l$ LetE (pvr,[],pty,rhs) acc)
      -- Finally reprocess teh whole thing
      tail (go (zip3 tmps tys ls) bod')

    -- We could eliminate these ahead of time:
    LetE (v,_,t,rhs) bod | isTrivial rhs ->
      T.LetTrivT (v,typ t, triv "<internal error2>" rhs) <$> tail bod

    -- TWO OPTIONS HERE: we could push equality prims into the target lang.
    -- Or we could map directly onto the IfEqT form:
    -- L1.IfE (L1.PrimAppE L1.EqP __ ) b c -> __

    IfE a b c       -> do b' <- tail b
                          c' <- tail c
                          lbl <- gensym "switch"
                          return $ T.Switch lbl (triv "if test" a)
                                      -- If we are treating the boolean as a tag, then tag "0" is false
                                      (T.IntAlts [(0, c')])
                                      -- And tag "1" is true:
                                      (Just b')

    LetE (vr, _, ty, L _ (L1.TimeIt rhs _ flg)) bod ->
        do rhs' <- tail rhs
           case ty of
             ProdTy ls ->
               do (tmps,bod') <- eliminateProjs vr ls bod
                  T.LetTimedT flg (zip tmps (L.map typ ls)) rhs' <$> tail bod'
             _ -> T.LetTimedT flg   [(vr, typ ty)]          rhs' <$> tail bod


    --------------------------------Start PrimApps----------------------------------
    -- (1) Primapps that become Tails:

    -- FIXME: No reason errors can't stay primitive at Target:
    PrimAppE (ErrorP str _ty) [] ->
      pure $ T.ErrT str

    LetE (_,_,_, L _ (PrimAppE (L1.ErrorP str _) [])) _ ->
      pure $ T.ErrT str

    -- Whatever... a little just-in-time flattening.  Should obsolete this:
    PrimAppE p ls -> do
      tmp <- gensym $ toVar "flt"
      tail (l$ LetE (tmp, [], primRetTy p, l$ PrimAppE p ls) (l$ VarE tmp))

    ---------------------
    -- (2) Next FAKE Primapps.  These could be added to L1 if we wanted to pollute it.

    LetE (v,_,_, L _ (Ext (ReadInt cur))) bod -> do
      vtmp <- gensym $ toVar "tmpval"
      ctmp <- gensym $ toVar "tmpcur"

      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L1.substE (l$ ProjE 0 (l$ VarE v)) (l$ VarE vtmp) $
                 L1.substE (l$ ProjE 1 (l$ VarE v)) (l$ VarE ctmp)
                 bod

      dbgTrace 5 (" [lower] ReadInt, after substing references to "
                  ++(fromVar v)++":\n  "++sdoc bod') <$>
        T.LetPrimCallT [(vtmp,T.IntTy),(ctmp,T.CursorTy)] T.ReadInt [T.VarTriv cur] <$>
          tail bod'

    LetE (v, _, _, L _ (Ext (WriteInt c e))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] T.WriteInt [triv "WriteTag arg" e, T.VarTriv c] <$>
         tail bod


    -- In Target, AddP is overloaded still:
    LetE (v,_, _, L _ (Ext (AddCursor c (L _ (Ext (InitSizeOfBuffer mul)))))) bod -> do
      size <- gensym (varAppend "sizeof_" v)
      T.LetPrimCallT [(size,T.IntTy)] (T.InitSizeOfBuffer mul) [] <$>
        T.LetPrimCallT [(v,T.CursorTy)] T.AddP [ triv "addCursor base" (l$ VarE c)
                                               , triv "addCursor offset" (l$ VarE size)] <$>
        tail bod

    LetE (v,_, _, L _ (Ext (AddCursor c e))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] T.AddP [ triv "addCursor base" (l$ VarE c)
                                             , triv "addCursor offset" e] <$>
         tail bod

    LetE (v,_, _, L _ (Ext (ReadTag cur))) bod -> do
      vtmp <- gensym $ toVar "tmptag"
      ctmp <- gensym $ toVar "tmpcur"

      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L1.substE (l$ ProjE 0 (l$ VarE v)) (l$ VarE vtmp) $
                 L1.substE (l$ ProjE 1 (l$ VarE v)) (l$ VarE ctmp)
                 bod

      dbgTrace 5 (" [lower] ReadTag, after substing references to "
                  ++(fromVar v)++":\n  "++sdoc bod') <$>
        T.LetPrimCallT [(vtmp,T.TagTyPacked),(ctmp,T.CursorTy)] T.ReadTag [T.VarTriv cur] <$>
          tail bod'
      -- error $ "lower: ReadTag not handled yet."


    LetE (cursOut,_, _, L _ (Ext (WriteTag dcon cursIn))) bod -> do
      T.LetPrimCallT [(cursOut,T.CursorTy)] T.WriteTag
        [ T.TagTriv (getTagOfDataCon ddefs dcon) , triv "WriteTag cursor" (l$ VarE cursIn) ] <$>
        tail bod

    LetE (v,_,_, L _ (Ext (NewBuffer mul))) bod -> do
      let toEndV = varAppend "end_"
      reg <- gensym "region"
      tl' <- T.LetPrimCallT [(reg,T.CursorTy),(v,T.CursorTy)] (T.NewBuffer mul) [] <$>
               tail bod
      -- The type shouldn't matter. PtrTy is not used often in current programs,
      -- and would be easy to spot.
      T.withTail (tl',T.PtrTy) $ \trvs ->
         (T.LetPrimCallT [] T.FreeBuffer [(T.VarTriv reg),(T.VarTriv v),(T.VarTriv (toEndV v))] $
            T.RetValsT trvs)

    LetE (v,_,_, L _ (Ext (ScopedBuffer mul))) bod -> do
      T.LetPrimCallT [(v,T.CursorTy)] (T.ScopedBuffer mul) [] <$>
         tail bod

    LetE (v,_,_, L _ (Ext (SizeOfPacked start end))) bod -> do
      T.LetPrimCallT [(v,T.IntTy)] T.SizeOfPacked [ T.VarTriv start, T.VarTriv end ] <$>
        tail bod

    LetE (v,_,_, L _ (Ext (SizeOfScalar w))) bod -> do
      T.LetPrimCallT [(v,T.IntTy)] T.SizeOfScalar [ T.VarTriv w ] <$>
        tail bod

    -- Just a side effect
    LetE(_,_,_, L _ (Ext (BoundsCheck i bound cur))) bod -> do
      let args = [T.IntTriv (fromIntegral i), T.VarTriv bound, T.VarTriv cur]
      T.LetPrimCallT [] T.BoundsCheck args <$> tail bod

    LetE(v,_,_, L _ (Ext (ReadCursor c))) bod -> do
      vtmp <- gensym $ toVar "tmpcur"
      ctmp <- gensym $ toVar "tmpaftercur"
      -- Here we lamely chase down all the tuple references and make them variables:
      let bod' = L1.substE (l$ ProjE 0 (l$ VarE v)) (l$ VarE vtmp) $
                 L1.substE (l$ ProjE 1 (l$ VarE v)) (l$ VarE ctmp)
                 bod
      T.LetPrimCallT [(vtmp,T.CursorTy),(ctmp,T.CursorTy)] T.ReadCursor [T.VarTriv c] <$>
        tail bod'

    LetE (v, _, _, L _ (Ext (WriteCursor cur e))) bod ->
      T.LetPrimCallT [(v,T.CursorTy)] T.WriteInt [triv "WriteCursor arg" e, T.VarTriv cur] <$>
         tail bod

    LetE (_, _, _, L _ (Ext (BumpRefCount end_r1 end_r2))) bod ->
      T.LetPrimCallT [] T.BumpRefCount [T.VarTriv end_r1, T.VarTriv end_r2] <$>
        tail bod

    Ext _ -> error $ "lower: unexpected extension" ++ sdoc ex0

    ---------------------
    -- (3) Proper primapps.
    LetE (v,_,t, L _ (PrimAppE p ls)) bod ->
        -- No tuple-valued prims here:
        T.LetPrimCallT [(v,typ t)]
             (prim p)
             (L.map (triv $ "prim rand "++show p) ls) <$>
             (tail bod)
    --------------------------------End PrimApps----------------------------------

    AppE v _ (L _ (MkProdE ls)) -> return $ T.TailCall ( v) (L.map (triv "operands") ls)
    AppE v _ e            -> return $ T.TailCall ( v) [triv "operand" e]


    -- Tail calls are just an optimization, if we have a Proj/App it cannot be tail:
    ProjE ix (L _ (AppE f _ e)) -> do
        tmp <- gensym $ toVar "prjapp"
        let ArrowTy (ProdTy inTs) _ = funty (fundefs # f)
        tail $ l$ LetE ( tmp
                       , []
                       , fmap (const ()) (inTs !! ix)
                       , l$ ProjE ix (l$ AppE f [] e))
                 (l$ VarE tmp)

    LetE (_,_,_, (L _ (L1.AppE f _ _))) _
        | M.notMember f fundefs -> error $ "Application of unbound function: "++show f

    -- Non-tail call:
    LetE (vr, _,t, projOf -> (stk, (L _ (L1.AppE f _ arg)))) bod -> do
        let ArrowTy _ outTy = funty (fundefs # f)
        let f' = cleanFunName f
        (vsts,bod') <- case outTy of
                        L1.ProdTy [] -> error "lower: FINISHME: unit valued function"
                        L1.ProdTy tys ->
                          case stk of
                            [] -> do (tmps,e) <- eliminateProjs vr (L.map (fmap (const ())) tys) bod
                                     return (zip tmps (L.map typ tys), e)
                            -- More than one should not currently be
                            -- possible (no nested tuple returns):
                            [ix] -> do garbages <- sequence [ gensym "garbage" | _ <- L.tail tys ]
                                       let (lead,trail) = L.splitAt ix garbages
                                       return ( zip (lead++[vr]++trail)
                                                    (L.map typ tys)
                                              , bod)
                            oth -> error $ "lower.tail.LetE: unexpected pattern" ++ show oth
                        _ -> return ([(vr,typ t)], bod)
        case unLoc arg of
          MkProdE es ->
               T.LetCallT vsts f' (L.map (triv "one of app rands") es) <$> (tail bod')
          _ -> T.LetCallT vsts f' [(triv "app rand") arg]       <$> (tail bod')


    LetE (v, _, t, L _ (IfE a b c)) bod -> do
      let a' = triv "if test" a
      b' <- tail b
      c' <- tail c
      case t of
        -- Finilize unarisation:
        ProdTy ls -> do
             (tmps,bod') <- eliminateProjs v ls bod
             T.LetIfT (zip tmps (L.map typ ls)) (a', b', c') <$> tail bod'
        _ -> T.LetIfT [(v, typ t)] (a', b', c') <$> tail bod


    _ -> error$ "lower: unexpected expression in tail position:\n  "++sdoc ex0


-- Helpers
--------------------------------------------------------------------------------

-- | View pattern for matching agaist projections of Foo rather than just Foo.
projOf :: L Exp3 -> ([Int], L Exp3)
projOf (L _ (ProjE ix e)) = let (stk,e') = projOf e
                           in (stk++[ix], e')
projOf e = ([],e)



{- Commented out in the older one too.

-- | Go under bindings and transform the very last return point.
chainTail :: T.Tail -> (T.Tail -> T.Tail) -> T.Tail
chainTail tl fn =
  case tl of
    T.LetCallT   bnd rat rnds bod -> T.LetCallT   bnd rat rnds (chainTail bod fn)
    T.LetPrimCallT bnd p rnds bod -> T.LetPrimCallT bnd p rnds (chainTail bod fn)
    T.LetTrivT  bnd           bod -> T.LetTrivT           bnd  (chainTail bod fn)
    T.LetIfT bnd pr bod           -> T.LetIfT           bnd pr (chainTail bod fn)
    T.LetAllocT lhs vals bod      -> T.LetAllocT     lhs vals  (chainTail bod fn)
    -- Question here is whether we plan to go under Ifs and Cases...
    -- T.IfE a b c -> T.IfE a (chainTail b fn) (chainTail c fn)
    oth -> fn oth

-- | Create the right kind of Target let binding based on the form of the RHS:a
mkLetTail :: (Var,L2.Ty, T.Tail) -> T.Tail -> T.Tail
mkLetTail (vr,ty,rhs) =
  case rhs of
    RetValsT [one] -> __
    _ -> __
-}

-- | Eliminate projections from a given tuple variable.  INEFFICIENT!
eliminateProjs :: Var -> [Ty3] -> L Exp3 -> SyM ([Var],L Exp3)
eliminateProjs vr tys bod =
 dbgTrace 5 (" [lower] eliminating "++show (length tys)++
             " projections on variable "++show vr++" in expr with types "
                                        ++show tys++":\n   "++sdoc bod) $
 do tmps <- mapM (\_ -> gensym "pvrtmp") [1.. (length tys)]
    let go _ [] acc =
            -- If there are ANY references left, we are forced to make the products:
            L1.subst vr (l$ MkProdE (L.map (l . VarE) tmps)) acc
        go ix ((pvr,_pty):rs) acc =
           go (ix+1) rs
             (L1.substE (l$ ProjE ix (l$ VarE vr)) (l$ VarE pvr) acc)
    let bod' = go 0 (zip tmps tys) bod
    return (tmps,bod')



mkLet :: (Var, Ty3, L Exp3) -> L Exp3 -> L Exp3
mkLet (v,t, L _ (LetE (v2, _,t2,rhs2) bod1)) bod2 = l$ LetE (v2,[],t2,rhs2) $
                                                    l$ LetE (v,[],t,bod1) bod2
mkLet (v,t,rhs) bod = l$ LetE (v,[],t,rhs) bod



triv :: String -> L Exp3 -> T.Triv
triv msg (L _ e0) =
  case e0 of
    (VarE x) -> T.VarTriv x
    (LitE x) -> T.IntTriv (fromIntegral x) -- TODO: back propogate Int64 toL1
    (LitSymE s) -> T.IntTriv $ fromIntegral $ product $ L.map ord $ fromVar s
    -- Bools become ints:
    (PrimAppE L1.MkTrue [])  -> T.IntTriv 1
    (PrimAppE L1.MkFalse []) -> T.IntTriv 0
    -- TODO: I think we should allow tuples and projection in trivials:

    -- Heck, let's map Unit onto Int too:
    (MkProdE []) -> T.IntTriv 0
--      (ProjE x1 x2) -> __
--      (MkProdE x) -> __
    _ | isTrivial e0 -> error $ "lower/triv: this function is written wrong.  "++
                         "It won't handle the following, which satisfies 'isTriv':\n "++sdoc e0++
                         "\nMessage: "++msg
    _ -> error $ "lower/triv, expected trivial in "++msg++", got "++sdoc e0

typ :: UrTy a -> T.Ty
typ t =
  case t of
    IntTy  -> T.IntTy
    SymTy  -> T.SymTy
    BoolTy -> T.IntTy
    ListTy{} -> error "lower/typ: FinishMe: List types"
    ProdTy xs -> T.ProdTy $ L.map typ xs
    SymDictTy x -> T.SymDictTy $ typ x
    -- t | isCursorTy t -> T.CursorTy
    PackedTy{} -> T.PtrTy
    CursorTy -> T.CursorTy -- Audit me
    PtrTy -> T.PtrTy

prim :: Prim Ty3 -> T.Prim
prim p =
  case p of
    AddP -> T.AddP
    SubP -> T.SubP
    MulP -> T.MulP
    DivP -> T.DivP
    ModP -> T.ModP
    EqSymP -> T.EqP
    EqIntP -> T.EqP
    LtP    -> T.LtP
    GtP    -> T.GtP
    SizeParam -> T.SizeParam
    DictInsertP ty -> T.DictInsertP $ typ ty
    DictLookupP ty -> T.DictLookupP $ typ ty
    DictEmptyP ty -> T.DictEmptyP $ typ ty
    DictHasKeyP ty -> T.DictHasKeyP $ typ ty

    ReadPackedFile mf tyc _ -> T.ReadPackedFile mf tyc

    MkNullCursor -> error$ "lower/prim: internal error, should not have got to here: "++show p
    ErrorP{}     -> error$ "lower/prim: internal error, should not have got to here: "++show p
    MkTrue       -> error "lower/prim: internal error. MkTrue should not get here."
    MkFalse      -> error "lower/prim: internal error. MkFalse should not get here."
    SymAppend    -> error "lower/prim: internal error. SymAppend should not get here."
    PEndOf       -> error "lower/prim: internal error. PEndOf shouldn't be here."
