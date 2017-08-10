{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

-- | An intermediate language with an effect system that captures traversals.

module Packed.FirstOrder.L2.Syntax
    ( LocExp, PreLocExp(..)
    , mapMExprs
    , progToEnv
    , Prog2

    -- * Temporary backwards compatibility, plus rexports
    , UrTy(..)
    , PreExp(..)
    , pattern SymTy
    , primRetTy

    -- * Extended language L2.0 with location types.
    , Exp2, E2Ext(..), Ty2

    -- -- * Convenience aliases
    -- , Ty, Exp

    -- * Conversion back to L1
    , revertToL1


    -- The following will be removed:

-- (Maybe) DEPRECATED:
    -- * Extended "L2.1", for inline packed:
    , pattern NamedVal

-- DEPRECATED:
    -- * Extended "L2.2", for after cursor insertion:
    , pattern WriteInt, pattern ReadInt, pattern NewBuffer
    , pattern ScopedBuffer, pattern AddCursor
    , isExtendedPattern
    , builtinTEnv
    , includeBuiltins

    -- * Example
    , add1Prog, withAdd1Prog
    )
    where

import Control.DeepSeq
import Data.List as L
import Data.Loc
import Data.Set as S
import Data.Map as M
import Text.PrettyPrint.GenericPretty

import Packed.FirstOrder.Common
import Packed.FirstOrder.GenericOps
import Packed.FirstOrder.L1.Syntax hiding (mapExprs, progToEnv, add1Prog)
import qualified Packed.FirstOrder.L1.Syntax as L1

--------------------------------------------------------------------------------

-- | Extended expressions, L2.  Monomorphic.
type Exp2 = E2 LocVar Ty2

-- | The extension that turns L1 into L2.
data E2Ext loc dec =
    LetRegionE Region                 (L (E2 loc dec)) -- ^ Not used until later on.
  | LetLocE    loc    (PreLocExp loc) (L (E2 loc dec)) -- ^ Bind a new location.
  | RetE [loc] Var     -- ^ Return a value together with extra loc values.
  | FromEndE loc -- ^ Bind a location from an EndOf location (for RouteEnds and after)
  deriving (Show, Ord, Eq, Generic, NFData)

instance (Out l, Out d) => Out (E2Ext l d)

instance (Out l, Out d, Show l, Show d) => Expression (E2Ext l d) where
  type LocOf (E2Ext l d) = l
  type TyOf (E2Ext l d)  = UrTy l


-- | L1 expressions extended with L2.  This is the polymorphic version.
-- Shorthand for recursions above.
type E2 l d = PreExp E2Ext l d

instance Read (E2 l d) where
instance Read (L (E2 l d)) where

-- | Define a location in terms of a different location.
data PreLocExp loc = StartOfLE Region
                   | AfterConstantLE Int -- ^ Number of bytes after.
                                    loc  -- ^ Location which this location is offset from.
                   | AfterVariableLE Var -- ^ Name of variable v. This loc is size(v) bytes after.
                                    loc  -- ^ Location which this location is offset from.
                   | InRegionLE Region
                   | FromEndLE  loc
                   deriving (Read, Show, Eq, Ord, Generic, NFData)

instance Out l => Out (PreLocExp l)

type LocExp = PreLocExp LocVar


--------------------------------------------------------------------------------

-- | L1 Types extended with abstract Locations.
type Ty2 = L1.UrTy LocVar

-- | Here we only change the types of FUNCTIONS:
type Prog2 = Prog Ty2 (L Exp2)

--------------------------------------------------------------------------------

-- | Abstract some of the differences of top level program types, by
--   having a common way to extract an initial environment.  The
--   initial environment has types only for functions.
progToEnv :: Prog2 -> Env2 (UrTy ())
progToEnv Prog{fundefs} =
    Env2 M.empty
         (M.fromList [ (funName,(fmap (\_->()) arrIn, fmap (\_->()) arrOut))
                     | FunDef{funName, funTy=ArrowTy{arrIn,arrOut}}
                     <- M.elems fundefs ])


-- TODO: beta-branch: REVAMP BELOW HERE
--------------------------------------------------------------------------------


-- | Retrieve all LocVars mentioned in a type
_getTyLocs :: Ty2 -> Set LocVar
_getTyLocs t =
    case t of
      IntTy  -> S.empty
      SymTy  -> S.empty
      BoolTy -> S.empty
      ProdTy ls     -> S.unions (L.map _getTyLocs ls)
      PackedTy _ lv -> S.singleton lv -- This is a tricky case:
      SymDictTy elt -> _getTyLocs elt
      -- TODO(chai):
      PtrTy (LRM lv _ _) elt -> S.union (S.singleton lv) (_getTyLocs elt)
      CursorTy (LRM lv _ _)  -> S.singleton lv
      ListTy{}               -> error "FINISHLISTS"


-- | Annotate a naked type with fresh location variables.
_tyWithFreshLocs :: Ty1 -> SyM Ty2
_tyWithFreshLocs t =
  case t of
    L1.Packed k -> PackedTy k <$> genLetter
    L1.IntTy    -> return IntTy
    L1.SymTy    -> return SymTy
    L1.BoolTy   -> return BoolTy
    L1.ProdTy l -> ProdTy <$> mapM _tyWithFreshLocs l
    L1.SymDictTy v  -> SymDictTy <$> _tyWithFreshLocs v
    L1.PackedTy _ _ -> error $ "tyWithFreshLocs: unexpected type: " ++ show t
    L1.PtrTy _ _    -> error $ "FINISHME: _tyWithFreshLocs PtrTy"
    L1.CursorTy _   -> error $ "FINISHME: _tyWithFreshLocs CursorTy"
    L1.ListTy _ -> error "tyWithFreshLocs: FIXME implement lists"

-- | Remove the extra location annotations.
_stripTyLocs :: Ty2 -> L1.Ty1
_stripTyLocs = fmap (const ())
  -- case t of
  --   PackedTy k _  -> L1.PackedTy k ()
  --   IntTy        -> L1.IntTy
  --   SymTy        -> L1.SymTy
  --   BoolTy       -> L1.BoolTy
  --   ProdTy l     -> L1.ProdTy    $ L.map stripTyLocs l
  --   SymDictTy v  -> L1.SymDictTy $ stripTyLocs v


-- | Apply a variable substitution to a type.
_substTy :: Map LocVar LocVar -> Ty2 -> Ty2
_substTy mp t = go t
  where
    go t =
     case t of
      IntTy  -> IntTy
      SymTy  -> SymTy
      BoolTy -> BoolTy
      SymDictTy te -> SymDictTy (go te)
      ProdTy    ts -> ProdTy    (L.map go ts)
      PackedTy k l ->
          case M.lookup l mp of
                Just v  -> PackedTy k v
                Nothing -> PackedTy k l
                -- errorWithStackTrace $ "substTy: failed to find "++show l++
                --   "\n  in map: "++show mp++", when processing type "++show t
      -- TODO(chai):
      PtrTy (LRM l reg mod) te ->
        case M.lookup l mp of
          Just v  -> PtrTy (LRM v reg mod) (go te)
          Nothing -> PtrTy (LRM l reg mod) (go te)
      CursorTy (LRM l reg mod) ->
        case M.lookup l mp of
          Just v  -> CursorTy (LRM v reg mod)
          Nothing -> CursorTy (LRM l reg mod)
      ListTy _ -> error "tyWithFreshLocs: FIXME implement lists"

-- | Apply a substitution to an effect set.
_substEffs :: Map LocVar LocVar -> Set Effect -> Set Effect
_substEffs mp ef =
    dbgTrace 5 ("\n  Substituting in effects "++show(mp,ef)) $
    S.map (\(Traverse v) ->
               case M.lookup v mp of
                 Just v2 -> Traverse v2
                 Nothing -> Traverse v) ef

-- | Collect all the locations mentioned in a type.
_allLocVars :: Ty2 -> [LocVar]
-- TODO: could just be a fold
_allLocVars t =
    case t of
      SymTy     -> []
      BoolTy    -> []
      IntTy     -> []
      PackedTy _ v  -> [v]
      ProdTy ls     -> L.concatMap _allLocVars ls
      SymDictTy elt -> _allLocVars elt
      PtrTy (LRM lv _ _) elt -> [lv] ++ _allLocVars elt
      CursorTy (LRM lv _ _)  -> [lv]
      ListTy _ -> error "allLocVars: FIXME lists"


-- Cursor types encoded into the current language
--------------------------------------------------------------------------------


-- -- Cursorizing arguments and returns -- abstracting the conventions
-- --------------------------------------------------------------------------------

-- -- _addOutputParamArgs = __


-- -- _addEndWitnessReturns = __

-- -- Cursorizing types.
-- --------------------------------------------------------------------------------
-- -- This happens in two stages, corresponding to the passes RouteEnds
-- -- and CursorDirect.

-- -- | Step 1/3: add additional outputs corresponding to
-- -- end-of-input-value witnesses.  Return the new type and the added
-- -- outputs.
-- cursorizeUrTy :: ArrowTy Ty -> (ArrowTy Ty, [LocVar])
-- cursorizeUrTy (ArrowTy inT ef ouT) = (newArr, newOut)
--  where
--   newArr = ArrowTy inT ef newOutTy
--   newOutTy = prependArgs (L.map mkCursorTy newOut)
--                          ouT
--   -- Every _traversed_ packed input means a POTENTIAL output (new
--   -- return value for the cursor's final value).
--   newOut   = [ toEndVar v  -- This determines the ORDER of added inputs.
--              | Traverse v <- S.toList ef ] -- ^ Because we traverse all outputs,
--                                            -- this effect set  is just what we need.

-- -- | Step 2/3: continue the conversion by:
-- --
-- --  (1) First, adding additional input arguments for the destination
-- --      cursors to which outputs are written.
-- --  (2) Packed types in the output then become end-cursors for those
-- --      same destinations.
-- --  (3) Packed types in the input STAY non-cursor packed types.
-- --
-- --  Results: the new type as well as the extra params added to the
-- --  input type.
-- cursorizeTy2 :: ArrowTy Ty -> (ArrowTy Ty, [LocVar])
-- cursorizeTy2 (ArrowTy inT ef ouT) =  (newArr, newIn)
--  where
--   newArr   = ArrowTy newInTy ef newOutTy
--   newInTy  = prependArgs (L.map mkCursorTy newIn) -- These are cursors
--                          inT -- These remain non-cursors.
--                          -- (mapPacked (\_ l -> mkCursorTy l) inT)
--   -- Let's turn output values into updated-output-cursors:
--   -- NOTE: we could distinguish between the (size ef) output cursors
--   -- that are already prepended here:
--   newOutTy = mapPacked (\_ l -> mkCursorTy (ensureEndVar l)) ouT
--   newIn    =
--    if S.null ef
--    then allLocVars ouT -- These stay in their original order (preorder)
--    else -- Strip the added output cursors off before computing this
--         let ProdTy ls = ouT in
--         allLocVars (ProdTy (L.drop (S.size ef) ls))

-- -- | Take the final step (3/3)
-- --   Packed types in the input now become (read-only) cursors.
-- cursorizeArrty3 :: ArrowTy Ty -> ArrowTy Ty
-- cursorizeArrty3 arr@(ArrowTy inT ef ouT) =
--     if hasRealPacked ouT
--     then error $"Bad input to cursorizeArrty3, has non-cursor packed outputs.  Was this put through cursorizeTy2?:+ "
--              ++show arr
--     else ArrowTy (cursorizeTy3 inT) ef ouT

-- -- | The non-arrow counterpart to `cursorizeArrTy3`
-- cursorizeTy3 :: Ty2 -> Ty2
-- cursorizeTy3  = mapPacked (\ _k l -> mkCursorTy l)


-- ensureEndVar :: Var -> Var
-- ensureEndVar v | isEndVar v = v
--                | otherwise  = toEndVar v

-- -- Injected cursor args go first in input and output:
-- prependArgs :: [Ty] -> Ty -> Ty
-- prependArgs [] t = t
-- prependArgs ls t = ProdTy $ ls ++ [t]


-- mapPacked :: (Var -> l -> UrTy l) -> UrTy l -> UrTy l
-- mapPacked fn t =
--   case t of
--     IntTy  -> IntTy
--     BoolTy -> BoolTy
--     SymTy  -> SymTy
--     (ProdTy x)    -> ProdTy $ L.map (mapPacked fn) x
--     (SymDictTy x) -> SymDictTy $ mapPacked fn x
--     PackedTy k l  -> fn (toVar k) l
--     ListTy{} -> error "FINISHLISTS"

-- --------------------------------------------------------------------------------

-- -- | Map every lexical variable in scope to an abstract location.
-- --   This is useful for compiler passes that need to track abstract
-- --   locations of program terms.
-- type LocEnv = M.Map Var Loc

-- -- | Convert the type of a function argument to an abstract location
-- -- for that function argument.
-- argtyToLoc :: Var -> Ty -> Loc
-- argtyToLoc v ty =
--  case ty of
--   PackedTy{}
--     | isCursorTy ty -> Fixed $ cursorTyLoc ty
--     | otherwise -> Fixed v
--     -- ^ Here we set the type based on the variable binding name, not the
--     -- quantified loc variable in the type signature.
--   (ProdTy ls)   -> TupLoc [argtyToLoc (subloc v i) t | (t,i) <- zip ls [1..]]
--    -- ^ Here we generate fixed locations that are *subparts* of the function argument.
--   SymTy         -> Bottom
--   IntTy         -> Bottom
--   BoolTy        -> Bottom
--   SymDictTy _t  -> -- ^ This may contain packed objects, but it is not contiguous.
--     Fixed v
--     -- if hasPacked t then Top else Bottom
--   ListTy _ -> error "allLocVars: FIXME lists"


-- -- A bit of name mangling when promoting lexical variables to location vars
-- ---------------------------------------------------------------------------
-- -- | First, lift program variables so they don't interfere with ones
-- -- we introduce.  Also, remove internal underscores.
-- mangle :: Var -> Var
-- mangle v = v
-- -- mangle v = "_" ++ L.filter (/='_') v

-- -- | Refer to a portion of the data associated with a var.
-- subloc :: Var -> Int -> Var
-- subloc v n = varAppend v (toVar (show n))

-- -- Strip off any subloc modifiers
-- -- root :: Var -> Var
-- ------------------------------------------------------------

-- -- | Take a location which is expected to be a single variable, and
-- -- retrieve that variable.
-- getLocVar :: Loc -> Maybe Var
-- getLocVar (Fresh v) = Just v
-- getLocVar (Fixed v) = Just v
-- getLocVar Top = Nothing
-- getLocVar l = error $"getLocVar: expected a single packed value location, got: "
--                     ++show(doc l)



-- -- | We extend the environment when going under lexical binders, which
-- -- always have fixed abstract locations associated with them.
-- extendLocEnv :: [(Var,L1.Ty)] -> LocEnv -> SyM LocEnv
-- extendLocEnv []    e     = return e
-- extendLocEnv ((v,t):r) e =
--     do t' <- tyWithFreshLocs t -- Temp, just to call argtyToLoc.
--        extendLocEnv r (M.insert v (argtyToLoc (mangle v) t') e)


-- -- FIXME: Remove:
-- mapExprs :: (Env2 (UrTy ()) -> Exp -> Exp) -> Prog -> Prog
-- mapExprs fn (Prog dd fundefs mainExp) =
--     Prog dd
--          (fmap (\ (FunDef nm arrTy@(ArrowTy inT _ _) arg bod) ->
--                  let env = Env2 (M.singleton arg (fmap (\_->()) inT))
--                                 funEnv
--                  in FunDef nm arrTy arg (fn env bod))
--             fundefs)
--          -- The function is implicitly assumed not to change the type!
--          -- TODO: perhaps should re-infer the type here?
--          (fmap (\(e,t) -> (fn (Env2 M.empty funEnv) e, t) ) mainExp)
--   where
--     funEnv = fEnv $ includeBuiltins $ progToEnv (Prog dd fundefs mainExp)

-- | Map exprs with an initial type environment:
mapMExprs :: Monad m => (Env2 (UrTy LocVar) -> L Exp2 -> m (L Exp2)) -> Prog2 ->
             m Prog2
mapMExprs = error $ "FINISHME: L2 mapMExprs"
-- mapMExprs fn (Prog dd fundefs mainExp) =
--     Prog dd <$>
--          (mapM (\ (FunDef nm arrTy@(ArrowTy inT _ _) arg bod) ->
--                  let env = Env2 (M.singleton arg (fmap (\_->()) inT))
--                                 funEnv
--                  in
--                    FunDef nm arrTy arg <$> (fn env bod))
--             fundefs)
--          <*>
--          (mapM (\ (e,t) ->
--                  (,t) <$> fn (Env2 M.empty funEnv) e) mainExp)
--   where
--     funEnv = fEnv $ includeBuiltins $ progToEnv (Prog dd fundefs mainExp)


--------------------------------------------------------------------------------

-- | Because L2 just adds a bit of metadata and enriched types, it is
-- possible to strip it back down to L1.
revertToL1 :: Prog2 -> L1.Prog1
revertToL1 = undefined -- TODO: Fix or remove this function
-- revertToL1 Prog{ ..} =
--   L1.Prog { L1.ddefs   = fmap (fmap (fmap (const ()))) ddefs
--           , L1.fundefs = M.map go fundefs
--           , L1.mainExp = fmap (exp . fst) mainExp
--           }
--  where
--    go FunDef{..} =
--        let ArrowTy{arrIn,arrOut} = funty in
--        L1.FunDef funname (funarg, stripTyLocs arrIn) (stripTyLocs arrOut) (exp funbod)
--    exp :: E2' () Ty -> L1.Exp
--    exp ex = mapExt (\(e::E2 () Ty) ->
--                     error $ "revertToL1: cannot revert, essential L2 construct used:\n  "++show e)
--                    (fmap stripTyLocs ex)


--------------------------------------------------------------------------------


-- Conventions encoded inside the existing Core IR
-- =============================================================================

-- For use after inlinePacked / before cursorize:
-------------------------------------------------

-- | Used to inline variable bindings while retaining their (former) name and type.
pattern NamedVal :: forall t t1 (t2 :: * -> * -> *).
                    Var -> t -> L (PreExp t2 t1 t) -> PreExp t2 t1 t
pattern NamedVal vr ty e <- LetE (vr,[],ty,e)
                                  (L _ (VarE (Var "NAMED_VAL_PATTERN_SYN")))
  where NamedVal vr ty e = LetE (vr,[],ty,e)
                                    (L NoLoc (VarE "NAMED_VAL_PATTERN_SYN"))


-- For use after cursorize:
--------------------------------------------------------------------------------

pattern NewBuffer :: forall t t1 (t2 :: * -> * -> *). PreExp t2 t1 t
pattern NewBuffer <- AppE (Var "NewBuffer") [] (L _ (MkProdE []))
  where NewBuffer = AppE "NewBuffer" [] (L NoLoc (MkProdE []))

-- | output buffer space that is known not to escape the current function.
pattern ScopedBuffer :: forall t t1 (t2 :: * -> * -> *). PreExp t2 t1 t
pattern ScopedBuffer <- AppE (Var "ScopedBuffer") [] (L _ (MkProdE []))
  where ScopedBuffer = AppE "ScopedBuffer" [] (L NoLoc (MkProdE []))

-- | Tag writing is still modeled by DataConE.
pattern WriteInt :: forall t t1 (t2 :: * -> * -> *).
                    Var -> L (PreExp t2 t1 t) -> PreExp t2 t1 t
pattern WriteInt v e <- AppE (Var "WriteInt") [] (L _ (MkProdE [L _ (VarE v), e]))
  where WriteInt v e = AppE "WriteInt" [] (L NoLoc (MkProdE [L NoLoc (VarE v), e]))

-- | One cursor in, (int,cursor') output.
pattern ReadInt :: forall t t1 (t2 :: * -> * -> *). Var -> PreExp t2 t1 t
pattern ReadInt v <- AppE (Var "ReadInt") [] (L _ (VarE v))
  where ReadInt v = AppE "ReadInt" [] (L NoLoc (VarE v))

-- | Add a constant offset to a cursor variable.
pattern AddCursor :: forall t t1 (t2 :: * -> * -> *).
                     Var -> Int -> PreExp t2 t1 t
pattern AddCursor v i <- AppE (Var "AddCursor") []
                               (L _ (MkProdE [L _ (VarE v), L _ (LitE i)]))
  where AddCursor v i = AppE "AddCursor" []
                                 (L NoLoc (MkProdE [L NoLoc (VarE v),
                                                    L NoLoc (LitE i)]))


-- | A predicate to check if the form is part of the extended "L2.5" language.
isExtendedPattern :: PreExp l e d -> Bool
isExtendedPattern e =
  case e of
    NewBuffer{}    -> True
    ScopedBuffer{} -> True
    ReadInt{}      -> True
    WriteInt{}     -> True
    AddCursor{}    -> True
    _              -> False


-- Initial type environments
--------------------------------------------------------------------------------

dummyCursorTy :: L1.Ty1
dummyCursorTy = CursorTy dummyLRM

-- | Return type for a primitive operation.
primRetTy :: Prim -> L1.Ty1
primRetTy p =
  case p of
    AddP -> IntTy
    SubP -> IntTy
    MulP -> IntTy
    Gensym  -> SymTy
    EqSymP  -> BoolTy
    EqIntP  -> BoolTy
    MkTrue  -> BoolTy
    MkFalse -> BoolTy
    MkNullCursor   -> dummyCursorTy
    SizeParam      -> IntTy
    DictHasKeyP _  -> BoolTy
    DictEmptyP ty  -> SymDictTy ty
    DictInsertP ty -> SymDictTy ty
    DictLookupP ty -> ty
    (ErrorP _ ty)  -> ty
    ReadPackedFile _ _ ty -> ty



-- | A type environment listing the types of built-in functions.
--
--   Using this table represents a policy decision.  Specifically,
--   that a type checker is relying on the fact that all the L2.5
--   patterns above are valid AppE forms.  The alternative is for that
--   typechecker to match against these patterns before the AppE
--   cases.
--
builtinTEnv :: M.Map Var (ArrowTy L1.Ty1)
builtinTEnv = undefined
  -- M.fromList
  -- [ ("NewBuffer",    ArrowTy voidTy S.empty dummyCursorTy)
  -- , ("ScopedBuffer", ArrowTy voidTy S.empty dummyCursorTy)
  -- , ("ReadInt",      ArrowTy dummyCursorTy S.empty (ProdTy [IntTy, dummyCursorTy]))
  -- , ("WriteInt",     ArrowTy (ProdTy [dummyCursorTy, IntTy]) S.empty dummyCursorTy)
  -- , ("AddCursor",    ArrowTy (ProdTy [dummyCursorTy, IntTy]) S.empty dummyCursorTy)
  -- -- Note: ReadPackedFile is a builtin/primitive.  It is polymorphic,
  -- -- which currently doesn't allow us to model it as a function like
  -- -- this [2017.01.08].
  -- ]

includeBuiltins :: Env2 (UrTy ()) -> Env2 (UrTy ())
includeBuiltins (Env2 _ _) = undefined
    -- Env2 v (f `M.union` f')
    -- where f' = M.fromList [ (n,(fmap (\_->()) a, fmap (\_->()) b))
    --                       | (n, ArrowTy a _ b) <- M.assocs builtinTEnv ]


-- Example
--------------------------------------------------------------------------------

-- | Our canonical simple example, written in this IR.
add1Prog :: Prog2
add1Prog = withAdd1Prog Nothing

-- | Supply a main expression to run with add1 defined.
withAdd1Prog :: Maybe (Ty2, L Exp2) -> Prog2
withAdd1Prog mainExp =
    let ddfs = ddtree
        funs = (M.fromList [("add1",exadd1)])
    in Prog ddfs funs mainExp
 where
  ddtree :: DDefs Ty2
  ddtree = (fromListDD [DDef "Tree"
                                [ ("Leaf",[(False,IntTy)])
                                , ("Node",[(False,PackedTy "Tree" "l")
                                          ,(False,PackedTy "Tree" "l")])]])

  exadd1 :: FunDef Ty2 (L Exp2)
  exadd1 = FunDef "add1" "tr" exadd1ty exadd1bod

  exadd1ty :: ArrowTy Ty2
  exadd1ty = (ArrowTy
             (PackedTy "tree" "lin")
             (PackedTy "tree" "lout")
             [LRM "lin" (VarR "r1") Input, LRM "lout" (VarR "r1") Output]
             (S.fromList [Traverse "lin"])
             [EndOf $ LRM "lin" (VarR "r1") Input])

  exadd1bod :: L Exp2
  exadd1bod =
      L NoLoc $ CaseE (L NoLoc $ VarE "tr") $
        [ ("Leaf", [("n","l0")], L NoLoc $
                                 LetE ("v",[],IntTy,L NoLoc $ PrimAppE L1.AddP
                                                    [L NoLoc $ VarE "n",
                                                     L NoLoc $ LitE 1])
                                 (L NoLoc $ VarE "v"))
        , ("Node", [("x","l1"),("y","l2")],
           L NoLoc $ Ext $ LetLocE "lout1" (AfterConstantLE 1 "lout") $
           L NoLoc $ LetE ("x1",[],PackedTy "Tree" "lout1",
                           L NoLoc $ AppE "add1" ["l1","lout1"] $
                           L NoLoc $ VarE "x") $
           L NoLoc $ Ext $ LetLocE "lout2" (AfterVariableLE "x1" "lout1") $
           L NoLoc $ LetE ("y1",[],PackedTy "Tree" "lout2",
                           L NoLoc $ AppE "add1" ["l2","lout2"] $
                           L NoLoc $ VarE "y") $
           L NoLoc $ LetE ("z",[],PackedTy "Tree" "lout",
                    L NoLoc $ DataConE "lout" "Node"
                    [ L NoLoc $ VarE "x1" , L NoLoc $ VarE "y1"]) $
           L NoLoc $ VarE "z")
        ]
