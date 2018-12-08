-- UNFINISHED?

module Gibbon.L0.Interp
    ( Value(..) )
  where
import           GHC.Generics
import           Data.Char
-- import           Data.IntMap as IM
import           Data.List as L
import           Data.Loc
import           Data.Map as M


import           Gibbon.Common
import           Gibbon.L0.Syntax as L0
import qualified Gibbon.L1.Syntax as L1

data Value = VInt Int
           | VBool Bool
           | VDict (M.Map Value Value)
--           | VList
           | VProd [Value]
           | VPacked DataCon [Value]
           | VCursor { bufID :: Int, offset :: Int }
           | VLam Var (L Exp0) ValEnv
           -- ^ Since L0 is higher order
     deriving(Read, Eq, Ord, Generic)

instance Show Value where
 show v =
  case v of
   VInt n   -> show n
   VBool b  -> if b then truePrinted else falsePrinted
   VProd ls -> "'#("++ concat(intersperse " " (L.map show ls)) ++")"
   VDict m      -> show (M.toList m)
   VPacked k ls -> "(" ++ k ++ concat (L.map ((" "++) . show) ls) ++ ")"
   VCursor idx off -> "<cursor "++show idx++", "++show off++">"
   VLam x e _ -> "<proc "++show x++", "++show e++">"

type ValEnv = Map Var Value


interpProg :: Prog -> Value
-- for now just call interp
interpProg Prog {ddefs,fundefs,mainExp=Just e} = interp M.empty e
  where
    interp :: ValEnv -> (L Exp0) -> Value
    interp env (L _ ex) =
      case ex of
        L1.Ext l0 ->
          case l0 of
            LambdaE v b  -> VLam v b env
            PolyAppE a d ->
              let rand = interp env d
                  lam  = interp env a
              in case lam of
                   VLam x b env' -> interp (M.insert x rand env') b
                   oth           -> error $ "L0.Interp: cannot apply " ++ show oth
        L1.VarE v -> env M.! v
        L1.LitE c -> VInt c
        L1.LitSymE c     -> VInt (strToInt $ fromVar c)
        L1.PrimAppE p ls -> applyPrim p $ L.map (interp env) ls
        L1.MkProdE ls    -> VProd $ L.map (interp env) ls
        L1.ProjE ix x    -> let (VProd ls) = interp env x in ls !! ix
        L1.AppE f _ b    ->
          let rand = interp env b in
            case M.lookup f fundefs of
              Just FunDef{funArg=(vr,_),funBody} -> interp (M.insert vr rand env) funBody
              Nothing -> error $ "L0.Interp: unbound function in application: "++ show ex
        L1.IfE a b c  ->
          case interp env a of
            VBool p -> if p then interp env b else interp env c
            oth     -> error $ "L0.Interp: expected boolean, got " ++ show oth
        L1.DataConE _ k ls -> VPacked k $ L.map (interp env) ls
        L1.CaseE _ []      -> error $ "L0.Interp: CaseE with empty alternatives list"
        L1.CaseE x alts    ->
          case interp env x of
            VPacked k ls -> let vs = L.map fst prs
                                (_,prs,rhs) = lookupCons k alts
                                env' = M.union (M.fromList (zip vs ls)) env
                            in interp env' rhs
            oth          -> error $ "L1.Interp: type error, expected data constructor, got: "++ show oth
        L1.LetE (v,_,_ty,rhs) bod ->
          let rhs' = interp env rhs
              env' = M.insert v rhs' env
          in interp env' bod
        L1.TimeIt bod _ _ -> interp env bod
        L1.MapE _ _bod    -> error "L0.Interp: finish MapE"
        L1.FoldE _ _ _bod -> error "L0.Interp: finish FoldE"

applyPrim :: L1.Prim Ty0 -> [Value] -> Value
applyPrim p vs =
   case (p,vs) of
     (L1.MkTrue,[])             -> VBool True
     (L1.MkFalse,[])            -> VBool False
     (L1.AddP,[VInt x, VInt y]) -> VInt (x+y)
     (L1.SubP,[VInt x, VInt y]) -> VInt (x-y)
     (L1.MulP,[VInt x, VInt y]) -> VInt (x*y)
     (L1.SymAppend,[VInt x, VInt y]) -> VInt (x * (strToInt $ show y))
     (L1.EqSymP,[VInt x, VInt y]) -> VBool (x==y)
     (L1.EqIntP,[VInt x, VInt y]) -> VBool (x==y)
     ((L1.DictInsertP _ty),[VDict mp, key, val]) -> VDict (M.insert key val mp)
     ((L1.DictLookupP _),[VDict mp, key])        -> mp M.! key
     ((L1.DictHasKeyP _),[VDict mp, key])        -> VBool (M.member key mp)
     ((L1.DictEmptyP _),[])                      -> VDict M.empty
     ((L1.ErrorP msg _ty),[]) -> error msg
     (L1.ReadPackedFile file _ ty,[]) ->
         error $ "L0.Interp: unfinished, need to read a packed file: "++show (file,ty)
     oth -> error $ "unhandled prim or wrong number of arguments: "++show oth

lookupCons :: (Eq k, Show k, Show a, Show b) => k -> [(k,a,b)] -> (k,a,b)
lookupCons k [] = error $ "lookupCons: key "++show k++"not found."
lookupCons k ((k1,a1,b1):r)
           | k1 == k   = (k1,a1,b1)
           | otherwise = lookupCons k r


strToInt :: String -> Int
strToInt = product . L.map ord
