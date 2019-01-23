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

import           Control.Monad.State ( MonadState )
import           Control.DeepSeq (NFData)
import           Data.List
import           Data.Loc
import           GHC.Generics
import           Text.PrettyPrint.GenericPretty
import           Text.PrettyPrint.HughesPJ as PP
import qualified Data.Set as S
import qualified Data.Map as M

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

--------------------------------------------------------------------------------

data MetaTv = Meta Int
  deriving (Read, Show, Eq, Ord, Generic, NFData)

instance Out MetaTv where
  doc (Meta i) = text "$" PP.<> doc i
  docPrec _ v = doc v

newMetaTv :: MonadState Int m => m MetaTv
newMetaTv = Meta <$> newUniq

newMetaTy :: MonadState Int m => m Ty0
newMetaTy = MetaTv <$> newMetaTv

newTyVar :: MonadState Int m => m TyVar
newTyVar = BoundTv <$> genLetter

data Ty0
 = IntTy
 | BoolTy
 | TyVar TyVar   -- Rigid/skolem type variables
 | MetaTv MetaTv -- Unification variables
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

-- | Straightforward parametric polymorphism.
data TyScheme = ForAll [TyVar] Ty0
 deriving (Show, Read, Eq, Ord, Generic, NFData)

-- instance FreeVars TyScheme where
--   gFreeVars (ForAll tvs ty) = gFreeVars ty `S.difference` (S.fromList tvs)

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

isFunTy :: Ty0 -> Bool
isFunTy ArrowTy{} = True
isFunTy _ = False

-- | Get the free TyVars from types; no duplicates in result.
tyVarsInTy :: Ty0 -> [TyVar]
tyVarsInTy ty = tyVarsInTys [ty]

-- | Like 'tyVarsInTy'.
tyVarsInTys :: [Ty0] -> [TyVar]
tyVarsInTys tys = foldr (go []) [] tys
  where
    go :: [TyVar] -> Ty0 -> [TyVar] -> [TyVar]
    go bound ty acc =
      case ty of
        IntTy  -> acc
        BoolTy -> acc
        TyVar tv -> if (tv `elem` bound) || (tv `elem` acc)
                    then acc
                    else tv : acc
        MetaTv _ -> acc
        ProdTy tys1     -> foldr (go bound) acc tys1
        SymDictTy ty1   -> go bound ty1 acc
        ArrowTy a b     -> go bound a (go bound b acc)
        PackedTy _ tys1 -> foldr (go bound) acc tys1
        ListTy ty1      -> go bound ty1 acc

-- | Get the MetaTvs from a type; no duplicates in result.
metaTvsInTy :: Ty0 -> [MetaTv]
metaTvsInTy ty = metaTvsInTys [ty]

-- | Like 'metaTvsInTy'.
metaTvsInTys :: [Ty0] -> [MetaTv]
metaTvsInTys tys = foldr go [] tys
  where
    go :: Ty0 -> [MetaTv] -> [MetaTv]
    go ty acc =
      case ty of
        MetaTv tv -> if tv `elem` acc
                     then acc
                     else tv : acc
        IntTy   -> acc
        BoolTy  -> acc
        TyVar{} -> acc
        ProdTy tys1     -> foldr go acc tys1
        SymDictTy ty1   -> go ty1 acc
        ArrowTy a b     -> go b (go a acc)
        PackedTy _ tys1 -> foldr go acc tys1
        ListTy ty1      -> go ty1 acc

-- | Like 'tyVarsInTy'.
tyVarsInTyScheme :: TyScheme -> [TyVar]
tyVarsInTyScheme (ForAll tyvars ty) = tyVarsInTy ty \\ tyvars

-- | Like 'metaTvsInTy'.
metaTvsInTyScheme :: TyScheme -> [MetaTv]
metaTvsInTyScheme (ForAll _ ty) = metaTvsInTy ty -- ForAll binds TyVars only

-- | Like 'metaTvsInTys'.
metaTvsInTySchemes :: [TyScheme] -> [MetaTv]
metaTvsInTySchemes tys = concatMap metaTvsInTyScheme tys

arrowTysInTy :: Ty0 -> [Ty0]
arrowTysInTy = go []
  where
    go acc ty =
      case ty of
        IntTy    -> acc
        BoolTy   -> acc
        TyVar{}  -> acc
        MetaTv{} -> acc
        ProdTy tys    -> foldl go acc tys
        SymDictTy a   -> go acc a
        ArrowTy a b   -> go (go acc a) b ++ [ty]
        PackedTy _ vs -> foldl go acc vs
        ListTy a -> go acc a

-- Hack. In the specializer, we'd like to know the type of the scrutinee.
-- However, there are few things that prevent us from deriving Typeable for L0.
--
-- Typeable uses the type 'UrTy' which is shared by the IR's L1, L2 and L3, but not L0.
-- L0 uses it's own type Ty0, which is not an instance of 'UrTy'.
-- Can we merge 'Ty0' and 'UrTy' ? Well we can, but we would end up polluting 'UrTy'
-- with type variables and function types, which should be unused after L0.
-- Or, we can have a special (Typeable L0), which is what recoverTy is.
-- ¯\_(ツ)_/¯
--
recoverTy :: DDefs0 -> Env2 Ty0 -> L Exp0 -> Ty0
recoverTy ddfs env2 (L _ ex)=
  case ex of
    VarE v       -> M.findWithDefault (error $ "recoverType: Unbound variable " ++ show v) v (vEnv env2)
    LitE _       -> IntTy
    LitSymE _    -> IntTy
    AppE v _ _   -> outTy $ fEnv env2 # v
    PrimAppE p _ -> primRetTy1 p
    LetE (v,_,t,_) e -> recoverTy ddfs (extendVEnv v t env2) e
    IfE _ e _        -> recoverTy ddfs env2 e
    MkProdE es       -> ProdTy $ map (recoverTy ddfs env2) es
    DataConE (ProdTy locs) c _ -> PackedTy (getTyOfDataCon ddfs c) locs
    DataConE loc c _ -> PackedTy (getTyOfDataCon ddfs c) [loc]
    TimeIt e _ _     -> recoverTy ddfs env2 e
    MapE _ e         -> recoverTy ddfs env2 e
    FoldE _ _ e      -> recoverTy ddfs env2 e
    ProjE i e ->
      case recoverTy ddfs env2 e of
        (ProdTy tys) -> tys !! i
        oth -> error$ "typeExp: Cannot project fields from this type: "++show oth
                      ++"\nExpression:\n  "++ sdoc ex
                      ++"\nEnvironment:\n  "++sdoc (vEnv env2)
    ParE a b -> ProdTy $ map (recoverTy ddfs env2) [a,b]
    CaseE _ mp ->
      let (c,args,e) = head mp
          args' = map fst args
      in recoverTy ddfs (extendsVEnv (M.fromList (zip args' (lookupDataCon ddfs c))) env2) e
    Ext ext ->
      case ext of
        LambdaE (v,t) bod ->
          recoverTy ddfs (extendVEnv v t env2) bod
        PolyAppE{} -> error "recoverTyep: TODO PolyAppE"
  where
    -- Return type for a primitive operation.
    primRetTy1 :: Prim Ty0 -> Ty0
    primRetTy1 p =
      case p of
        AddP -> IntTy
        SubP -> IntTy
        MulP -> IntTy
        DivP -> IntTy
        ModP -> IntTy
        ExpP -> IntTy
        RandP-> IntTy
        EqSymP  -> BoolTy
        EqIntP  -> BoolTy
        LtP  -> BoolTy
        GtP  -> BoolTy
        OrP  -> BoolTy
        LtEqP-> BoolTy
        GtEqP-> BoolTy
        AndP -> BoolTy
        MkTrue  -> BoolTy
        MkFalse -> BoolTy
        SymAppend      -> IntTy
        SizeParam      -> IntTy
        DictHasKeyP _  -> BoolTy
        DictEmptyP ty  -> SymDictTy ty
        DictInsertP ty -> SymDictTy ty
        DictLookupP ty -> ty
        (ErrorP _ ty)  -> ty
        ReadPackedFile _ _ _ ty -> ty
        PEndOf -> error "primRetTy: PEndOf not handled yet"


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
