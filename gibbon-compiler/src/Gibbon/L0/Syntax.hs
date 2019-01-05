{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass    #-}

-- | A higher-ordered surface language that supports Rank-1 parametric
-- polymorphism.
module Gibbon.L0.Syntax
  ( module Gibbon.L0.Syntax,
    module Gibbon.Language,
  )
where

import           Control.DeepSeq (NFData)
import           Data.List
import           Data.Loc
import           GHC.Generics
import           Text.PrettyPrint.GenericPretty
import qualified Data.Set as S

import           Gibbon.Common as C
import           Gibbon.Language hiding (UrTy(..))

--------------------------------------------------------------------------------

type Exp0     = PreExp E0Ext Ty0 Ty0
type DDefs0   = DDefs Ty0
type DDef0    = DDef Ty0
type FunDef0  = FunDef (L Exp0)
type FunDefs0 = FunDefs (L Exp0)
type Prog0    = Prog (L Exp0)

--------------------------------------------------------------------------------

-- | The extension point for L0.
data E0Ext loc dec =
   LambdaE (Var,dec) -- Variable tagged with type
           (L (PreExp E0Ext loc dec))
 | PolyAppE (L (PreExp E0Ext loc dec)) -- Operator
            (L (PreExp E0Ext loc dec)) -- Operand
 deriving (Show, Ord, Eq, Read, Generic, NFData)

instance FreeVars (E0Ext l d) where
  gFreeVars e =
    case e of
      LambdaE (x,_) bod -> S.delete x $ gFreeVars bod
      PolyAppE f d  -> gFreeVars f `S.union` gFreeVars d

instance (Out l, Out d, Show l, Show d) => Expression (E0Ext l d) where
  type LocOf (E0Ext l d) = l
  type TyOf (E0Ext l d)  = d
  isTrivial _ = False

instance (Show l, Out l) => Flattenable (E0Ext l Ty0) where
    gFlattenGatherBinds _ddfs _env ex = return ([], ex)
    gFlattenExp _ddfs _env ex = return ex

instance (Out l, Show l, Typeable (L (PreExp E0Ext l Ty0))) => Typeable (E0Ext l Ty0) where
  gTypeExp ddfs env2 ex =
    case ex of
      LambdaE (_,t) b -> ArrowTy t $ gTypeExp ddfs env2 b
      PolyAppE f d ->
        case gTypeExp ddfs env2 f of
          ArrowTy t1 t2 -> let dt = gTypeExp ddfs env2 d in
                           if t1 == dt then t2 else
                             error $ "typeExp: PolyApp: Expected " ++ show t1
                             ++ "\n Actual " ++ show dt ++ "\n in " ++ show ex
          err           -> error $ "typeExp: Not an arrow type: " ++ show err
                                               ++ "\n in " ++ show ex

instance (Out l, Show l, Typeable (L (PreExp E0Ext l Ty0)),
          TyOf (E0Ext l Ty0) ~ TyOf (L (E0Ext l Ty0)),
          Expression (L (E0Ext l Ty0)))
         => Typeable (L (E0Ext l Ty0)) where
  gTypeExp ddfs env2 (L _ ex) = gTypeExp ddfs env2 ex

instance (Out l, Out d) => Out (E0Ext l d)
instance Out Ty0
instance Out TyScheme

data Ty0
 = IntTy
 | BoolTy
 | TyVar TyVar
 | ProdTy [Ty0]
 | SymDictTy Ty0
 | ArrowTy Ty0 Ty0
 | PackedTy TyCon [Ty0] -- Type arguments to the type constructor
 | ListTy Ty0
 deriving (Show, Read, Eq, Ord, Generic, NFData)

instance FunctionTy Ty0 where
  type ArrowTy Ty0 = TyScheme
  inTy  = arrIn
  outTy = arrOut

instance FreeVars Ty0 where
  gFreeVars ty =
    case ty of
      IntTy   -> S.empty
      BoolTy  -> S.empty
      TyVar v -> S.singleton v
      ProdTy tys     -> foldr (S.union . gFreeVars) S.empty tys
      SymDictTy ty1  -> gFreeVars ty1
      ArrowTy a b    -> gFreeVars a `S.union` gFreeVars b
      PackedTy _ tys -> foldr (S.union . gFreeVars) S.empty tys
      ListTy ty1     -> gFreeVars ty1

-- | Straightforward parametric polymorphism.
data TyScheme = ForAll [TyVar] Ty0
 deriving (Show, Read, Eq, Ord, Generic, NFData)

instance FreeVars TyScheme where
  gFreeVars (ForAll tvs ty) = gFreeVars ty `S.difference` (S.fromList tvs)

arrIn :: TyScheme -> Ty0
arrIn (ForAll _ (ArrowTy i _)) = i
arrIn err = error $ "arrIn: Not an arrow type: " ++ show err

arrOut :: TyScheme -> Ty0
arrOut (ForAll _ (ArrowTy _ o)) = o
arrOut err = error $ "arrOut: Not an arrow type: " ++ show err

arrIn' :: Ty0 -> Ty0
arrIn' (ArrowTy i _) = i
arrIn' err = error $ "arrIn': Not an arrow type: " ++ show err

tyFromScheme :: TyScheme -> Ty0
tyFromScheme (ForAll _ a) = a

tyVarsFromScheme :: TyScheme -> [TyVar]
tyVarsFromScheme (ForAll a _) = a

--------------------------------------------------------------------------------

tyVarsInType :: Ty0 -> [TyVar]
tyVarsInType = go []
  where
    go acc ty =
      case ty of
        IntTy   -> acc
        BoolTy  -> acc
        TyVar v -> if elem v acc
                   then acc
                   else acc ++ [v]
        ProdTy tys    -> foldl go acc tys
        SymDictTy a   -> go acc a
        ArrowTy a b   -> go (nub $ acc ++ tyVarsInType a) b
        PackedTy _ vs -> foldl go acc vs
        ListTy a -> go acc a

-- | Similar to 'voidTy'.
voidTy' :: Ty0
voidTy' = ProdTy []

{-

-- | Variable definitions

-- ^ Monomorphic version
data VarDef a ex = VarDef { varName :: Var
                          , varTy   :: a
                          , varBody :: ex }
  deriving (Show, Eq, Ord, Generic, NFData)

type VarDefs a ex = M.Map Var (VarDef a ex)

type FunDefs0 = M.Map Var FunDef0

type FunDef0 = FunDef (L Exp0)

instance FunctionTy Ty0 where
  type ArrowTy Ty0 = (Ty0 , Ty0)
  inTy = fst
  outTy = snd

-- ^ Polymorphic version

data PVDef a ex = PVDef { vName :: Var
                        , vTy   :: Scheme a
                        , vBody :: ex }
  deriving (Show, Read, Eq, Ord, Generic, NFData)

type PVDefs a ex = M.Map Var (PVDef a ex)

-- | for now, using a specialized DDef for L0
-- this enables the DDefs to have type variables
type PDDefs a = M.Map Var (PDDef a)

data PDDef a = PDDef { dName :: Var
                     , dCons :: [(DataCon,[(IsBoxed,Scheme a)])] } -- ^ Polymorphic data constructors
  deriving (Read,Show,Eq,Ord, Generic)


-- | for now, using a specialized FunDef for L0
-- theoretically these should disappear after monomorphization
-- this enables the FunDefs to have type schemes
type PFDefs a ex = M.Map Var (PFDef a ex)

data PFDef a ex  = PFDef { fName :: Var
                         , fArg  :: Var
                         , fTy   :: Scheme a -- ^ the type will be a ForAll
                         , fBody :: ex }
  deriving (Read,Show,Eq,Ord, Functor, Generic)

-- ^ Polymorphic program
data PProg = PProg { pddefs    :: PDDefs Ty0
                   , pfundefs  :: PFDefs Ty0 (L Exp0)
                   , pvardefs  :: PVDefs Ty0 (L Exp0)
                   , pmainExp  :: Maybe (L Exp0)
                   }
  deriving (Show, Eq, Ord, Generic)

-- ^ Monomorphic program
data MProg = MProg { ddefs    :: DDefs Ty0
                   , fundefs  :: FunDefs0
                   , vardefs  :: VarDefs Ty0 (L Exp0)
                   , mainExp  :: Maybe (L Exp0)
                   }
  deriving (Show, Eq, Ord, Generic)

-- | some type defns to make things look cleaner
type Exp = (L Exp0)

-- | we now have curried functions and curried calls
-- curried functions are these variable defns
-- but curried calls vs function calls are PolyAppE vs AppE
type CurFun  = VarDef Ty0 Exp
type CCall = Exp

-- | Monomorphized functions
type L0Fun = FunDef0
type FCall = Exp

arrIn :: Ty0 -> Ty0
arrIn (ArrowTy i _) = i
arrIn err = error $ "arrIn: Not an arrow type: " ++ show err

arrOut :: Ty0 -> Ty0
arrOut (ArrowTy _ o) = o
arrOut err = error $ "arrOut: Not an arrow type: " ++ show err

typeFromScheme :: Scheme a -> a
typeFromScheme (ForAll _ a) = a

initFunEnv :: PFDefs Ty0 Exp -> FunEnv Ty0
initFunEnv fds = M.foldr (\fn acc -> let fnTy = typeFromScheme (fTy fn)
                                         fntyin  = arrIn fnTy
                                         fntyout = arrOut fnTy
                                     in M.insert (fName fn) (fntyin, fntyout) acc)
                 M.empty fds

initVarEnv :: PVDefs Ty0 Exp -> M.Map Var Ty0
initVarEnv vds = M.foldr (\v acc -> M.insert (vName v) (typeFromScheme (vTy v)) acc)
                 M.empty vds
-}
