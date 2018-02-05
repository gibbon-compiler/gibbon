{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

-- | An intermediate language which makes cursors explicit

module Packed.FirstOrder.L3.Syntax
  (
    -- * Extended language
    Exp3, E3Ext(..), Ty3
  , Prog(..), FunDef(..), FunDefs, ArrowTy(..)

    -- * Functions
  , eraseLocMarkers, stripTyLocs, cursorizeArrowTy, mapMExprs, toL3Prim, progToEnv
  , cursorizeTy
  )
where

import Control.DeepSeq
import Data.Loc
import Data.Map as M
import Data.Set as S
import Data.List as L
import Text.PrettyPrint.GenericPretty

import Packed.FirstOrder.Common hiding (FunDef, FunDefs)
import Packed.FirstOrder.L1.Syntax hiding (FunDef(..), FunDefs, Prog(..), progToEnv)
import Packed.FirstOrder.GenericOps
import Packed.FirstOrder.L1.Syntax (UrTy(..), PreExp(..))
import qualified Packed.FirstOrder.L2.Syntax as L2

--------------------------------------------------------------------------------

type Exp3 = E3 () Ty3

-- |
type Ty3 = UrTy ()

-- | The extension that turns L1 into L3.
data E3Ext loc dec =
    ReadInt   Var                  -- ^ One cursor in, (int, cursor') out
  | WriteInt  Var (L (E3 loc dec)) -- ^ Write int at cursor, and return a cursor
  | AddCursor Var (L (E3 loc dec)) -- ^ Add a constant offset to a cursor variable
  | ReadTag   Var                  -- ^ One cursor in, (tag,cursor) out
  | WriteTag  DataCon Var          -- ^ Write Tag at Cursor, and return a cursor
  | NewBuffer                      -- ^ Create a new buffer, and return a cursor
  | ScopedBuffer                   -- ^ Create a temporary scoped buffer, and
                                   --   return a cursor
  | SizeOfPacked Var Var           -- ^ Takes in start and end cursors, and returns an Int
                                   --   sizeof(x) = (end_x - start_x) / sizeof(INT)
  | SizeOfScalar Var               -- ^ sizeof(var)
  deriving (Show, Ord, Eq, Read, Generic, NFData)

-- | L1 expressions extended with L3.  This is the polymorphic version.
-- Shorthand for recursions above.
type E3 l d = PreExp E3Ext l d

instance FreeVars (E3Ext l d) where
  gFreeVars  e =
    case e of
      ReadInt  v     -> S.singleton v
      WriteInt v ex  -> S.insert v (gFreeVars ex)
      AddCursor v ex -> S.insert v (gFreeVars ex)
      ReadTag v      -> S.singleton v
      WriteTag _ v   -> S.singleton v
      NewBuffer      -> S.empty
      ScopedBuffer   -> S.empty
      SizeOfPacked c1 c2 -> S.fromList [c1, c2]
      SizeOfScalar v     -> S.singleton v

instance (Out l, Out d) => Out (E3Ext l d)

instance (Out l, Out d, Show l, Show d) => Expression (E3Ext l d) where
  type LocOf (E3Ext l d) = l
  type TyOf  (E3Ext l d) = UrTy l
  isTrivial e =
    case e of
      ReadInt{}      -> False
      WriteInt{}     -> False
      AddCursor{}    -> False
      ReadTag{}      -> False
      WriteTag{}     -> False
      NewBuffer      -> False
      ScopedBuffer   -> False
      SizeOfPacked{} -> False
      SizeOfScalar{} -> False

instance (Out l, Show l) => Typeable (E3Ext l (UrTy l)) where
    gTypeExp = error "L3.gTypeExp"

instance (Show l, Out l) => Flattenable (E3Ext l (UrTy l)) where
    gFlattenGatherBinds _ddfs _env ex = return ([], ex)
    gFlattenExp _ddfs _env ex = return ex

data ArrowTy t = ArrowTy { arrIn  :: t
                         , arrOut :: t
                         }
  deriving (Show, Ord, Eq, Generic, NFData)

instance (Out t) => Out (ArrowTy t)

data FunDef = FunDef { funname :: Var
                     , funty   :: ArrowTy Ty3
                     , funarg  :: Var
                     , funbod  :: L Exp3
                     }
  deriving (Show, Ord, Eq, Generic, NFData)

instance Out FunDef

type FunDefs = M.Map Var FunDef

-- | Other than Exp3, everything is identical to L2
data Prog = Prog { ddefs   :: DDefs Ty3
                 , fundefs :: FunDefs
                 , mainExp :: Maybe (L Exp3, Ty3)
                 }
  deriving (Show, Ord, Eq, Generic, NFData)

instance Out Prog

-- | Erase LocVar markers from the data definition
eraseLocMarkers :: DDef L2.Ty2 -> DDef Ty3
eraseLocMarkers (DDef tyname ls) = DDef tyname $ L.map go ls
  where go :: (DataCon,[(IsBoxed,L2.Ty2)]) -> (DataCon,[(IsBoxed,Ty3)])
        go (dcon,ls') = (dcon, L.map (\(b,ty) -> (b,stripTyLocs ty)) ls')

-- | Remove the extra location annotations.
stripTyLocs :: UrTy a -> Ty3
stripTyLocs ty =
  case ty of
    IntTy     -> IntTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map stripTyLocs ls
    SymDictTy ty'    -> SymDictTy $ stripTyLocs ty'
    PackedTy tycon _ -> PackedTy tycon ()
    ListTy ty'       -> ListTy $ stripTyLocs ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy

cursorizeTy :: UrTy a -> UrTy b
cursorizeTy ty =
  case ty of
    IntTy     -> IntTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map cursorizeTy ls
    SymDictTy ty' -> SymDictTy $ cursorizeTy ty'
    PackedTy{}    -> ProdTy [CursorTy, CursorTy]
    ListTy ty'    -> ListTy $ cursorizeTy ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy


-- |
cursorizeArrowTy :: L2.ArrowTy L2.Ty2 -> ArrowTy Ty3
cursorizeArrowTy L2.ArrowTy{L2.arrIn,L2.arrOut,L2.locVars,L2.locRets} =
  let
      -- Adding additional outputs corresponding to end-of-input-value witnesses
      -- We've already computed additional location return value in RouteEnds
      rets = L.map (\_ -> CursorTy) locRets
      outT = L2.prependArgs rets arrOut

      -- Packed types in the output then become end-cursors for those same destinations.
      newOut = L2.mapPacked (\_ _ -> ProdTy [CursorTy, CursorTy]) outT

      -- Adding additional input arguments for the destination cursors to which outputs
      -- are written.
      mOutCurs = L.filter (\(LRM _ _ m) -> m == Output) locVars
      inT      = L2.prependArgs (L.map (\_ -> CursorTy) mOutCurs) arrIn

      -- Packed types in the input now become (read-only) cursors.
      newIn    = L2.mapPacked (\_ _ -> CursorTy) inT

  in ArrowTy { arrIn = stripTyLocs newIn, arrOut = stripTyLocs newOut }


-- | Map exprs with an initial type environment:
-- Exactly the same function that was in L2 before
mapMExprs :: Monad m => (Env2 Ty3 -> L Exp3 -> m (L Exp3)) -> Prog -> m Prog
mapMExprs fn (Prog ddfs fundefs mainExp) =
  Prog ddfs <$>
    (mapM (\f@FunDef{funarg,funty,funbod} ->
              let env = Env2 (M.singleton funarg (arrIn funty)) funEnv
              in do
                bod' <- fn env funbod
                return $ f { funbod =  bod' })
     fundefs)
    <*>
    (mapM (\ (e,t) -> (,t) <$> fn (Env2 M.empty funEnv) e) mainExp)
  where funEnv = M.map (\f -> let ty = funty f
                              in (arrIn ty, arrOut ty))
                 fundefs

-- Ugh .. this is bad. Can we remove the identity cases here ?
toL3Prim :: Prim L2.Ty2 -> Prim Ty3
toL3Prim pr =
  case pr of
    AddP      -> AddP
    SubP      -> SubP
    MulP      -> MulP
    DivP      -> DivP
    ModP      -> ModP
    EqSymP    -> EqSymP
    EqIntP    -> EqIntP
    LtP       -> LtP
    GtP       -> GtP
    MkTrue    -> MkTrue
    MkFalse   -> MkFalse
    SizeParam -> SizeParam
    SymAppend -> SymAppend
    DictInsertP ty -> DictInsertP (stripTyLocs ty)
    DictLookupP ty -> DictLookupP (stripTyLocs ty)
    DictEmptyP  ty -> DictEmptyP  (stripTyLocs ty)
    DictHasKeyP ty -> DictHasKeyP (stripTyLocs ty)
    ErrorP s ty    -> ErrorP s (stripTyLocs ty)
    ReadPackedFile fp tycon ty -> ReadPackedFile fp tycon (stripTyLocs ty)
    MkNullCursor -> MkNullCursor

-- | Abstract some of the differences of top level program types, by
-- having a common way to extract an initial environment.
progToEnv :: Prog -> Env2 Ty3
progToEnv Prog{fundefs} =
    Env2 M.empty
         (M.fromList [ (funname ,(inT, outT))
                     | FunDef{funty,funname} <- M.elems fundefs ,
                     let inT = arrIn funty
                         outT = arrOut funty])
