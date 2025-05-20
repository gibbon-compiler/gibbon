module Gibbon.Passes.Cursorize
  (cursorize) where

import           Control.Monad (forM)
import qualified Data.List as L
import qualified Data.Map as M
import           Data.Maybe (fromJust, listToMaybe)
import           Text.PrettyPrint.GenericPretty
import           Data.Foldable ( foldlM, foldrM )

import           Gibbon.DynFlags
import           Gibbon.Common
import           Gibbon.NewL2.Syntax
import           Gibbon.L3.Syntax hiding ( BoundsCheck, RetE, GetCilkWorkerNum, LetAvail,
                                           AllocateTagHere, AllocateScalarsHere, SSPush, SSPop,
                                           TagCursor )
import qualified Gibbon.L3.Syntax as L3
import           Gibbon.Passes.AddRAN ( numRANsDataCon )
import Data.Set (Set)

{-

Cursor insertion, strategy one:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we go to a "dilated" representation of packed values, where
every `Packed T` is represented by a pair, `(Cursor,Cursor)`,
i.e. start/end. Except function arguments, and variables bound by
by a pattern match. They're just `start` cursors.

REASONING: Why the dilated convention?  In a word: conditionals.  At the
end of each function body we need to return the appropriate end cursors.
But during the computation, we may need to add an arbitrary amount of
extra state to the return type of a conditional.  Thus it's difficult to
do this routing of information without changing the types of intermediate
expressions significantly.  Dilation is the current strategy.

We proceed with two loops, corresponding to packed and unpacked
context.  When the type of the current expression satisfies
`hasPacked`, that's when we're in packed context.  And, when in
packed context, we return dilated values.


E.g.
   
    type Tree = Leaf Int | Node Tree Tree

    add1 :: Tree -> Tree
    add1 tr =
      case tr of
        Leaf n   -> Leaf (n + 1)
        Node l r -> Node (add1 l) (add1 r)

becomes

    -- char*
    type Cursor = Ptr Char

    add1 :: Cursor -> Cursor -> (Cursor, (Cursor, Cursor))
    add1 lout lin =
      let tag = readTag lin
      in case tag of
           Leaf -> let n  = readInt tag
                       wt = writeTag lout Leaf
                       wi = writeInt wt   (n+1)
                   in (lin + 8, (lout, wi))
           Node -> ...

Every packed input becomes a read cursor. And it takes additional output cursors
for every packed type in the return value. Every packed return value becomes a
(Cursor,Cursor) i.e (start,end). And it returns additional end_of_read cursors
if the functions "traverses" it's input (more details in the paer).

    [VS]
    -- SoA representation 
    -- char*
    type Cursor = Ptr Char
    type CursorArray_${Int} = Cursor[Int] 

    CursorArray_2 = {Cursor, Cursor}
      where: 
        CursorArray_2[0] = tag buffer cursor
        CursorArray_2[1] = integer buffer cursor (Leaf)

    add1 :: CursorArray_2 -> CursorArray_2 -> (CursorArray_2, (CursorArray_2, CursorArray_2))
    add1 lout lin =
      let tag = readTag lin[0]
      in case tag of
           Leaf -> let n  = readInt lin[1]
                       wt = writeTag lout[0] Leaf
                       wi = writeInt lout[1] (n+1)
                   in ({lin[0] + 1, lin[1] + 8}, (lout, {lout[0] + 1, lout[1] + 8}))
           Node -> ...
-}


-- | Track variables depending on location variables.
--
--   If we have to create binding of the form `let v = loc` (in case expressions for example),
--   but `loc` is not bound yet, we'll add the variable to this map.
--   This is a stupid/simple way to get rid of FindWitnesses.
--   See `FindWitnesses.hs` for why that is needed.
-- For both locs and regions
type DepEnv = M.Map FreeVarsTy [(Var,[()],Ty3,Exp3)]

-- | Things we cannot define until we see a join point. There's a Ty2 to so that
-- we can extend the environment.
type SyncEnv = M.Map Var [(Var,[()],Ty3,Ty2,Exp3)]

type OldTy2 = UrTy LocVar

data WindowIntoCursor = AoSWin Var | SoAWin Var [((DataCon, Int), Var)]

-- |
cursorize :: Prog2 -> PassM Prog3
cursorize Prog{ddefs,fundefs,mainExp} = do
  dflags <- getDynFlags
  let useSoA = gopt Opt_Packed_SoA dflags
  fns' <- mapM (cursorizeFunDef useSoA ddefs fundefs . snd) (M.toList fundefs)
  let fundefs' = M.fromList $ L.map (\f -> (funName f, f)) fns'
      ddefs'   = M.map eraseLocMarkers ddefs

  {- VS: TODO: Ensure that the map passed to these functions contains the correct values, rn just passing empty maps -}    
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (e,ty) -> do
                  if hasPacked (unTy2 ty)
                  then Just . (, stripTyLocs (unTy2 ty)) <$>
                         fromDi <$> cursorizePackedExp M.empty M.empty ddefs fundefs M.empty M.empty M.empty e
                  else Just . (,stripTyLocs (unTy2 ty)) <$>
                         cursorizeExp M.empty M.empty ddefs fundefs M.empty M.empty M.empty e
  pure (Prog ddefs' fundefs' mainExp')

mangle :: [Var] -> Var 
mangle vars = toVar $ "mangle" ++ (L.foldr (\v acc -> acc ++ "_" ++ (fromVar v)) "" vars)

-- |
cursorizeFunDef :: Bool -> DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef3
cursorizeFunDef useSoA ddefs fundefs FunDef{funName,funTy,funArgs,funBody,funMeta} = do
  let inLocs  = inLocVars funTy
      outLocs = outLocVars funTy
      outRegs = outRegVars funTy
      inRegs  = inRegVars funTy
      in_tys  = arrIns funTy
      out_ty  = arrOut funTy
      funTy'  = cursorizeArrowTy useSoA funTy

      -- [2019.03.04] CSK: the order of these new cursor/region arguments isn't
      -- intuitive and can be improved.

      -- Input & output regions are always inserted before all other arguments.
      -- {- VS: adding toEndVRegVar may be useless -}
      regBinds = map toEndVRegVar (inRegs ++ outRegs)

      -- Output cursors after that.
      outCurBinds = outLocs

      freeVarToVarEnv = M.empty
      freeVarsInScope = (L.map fromLocVarToFreeVarsTy outCurBinds) ++ (L.map fromRegVarToFreeVarsTy regBinds) ++ (L.map fromVarToFreeVarsTy funArgs) ++ (L.map fromLocVarToFreeVarsTy inLocs)
      -- freeVarToVarEnv' = L.foldr (\fv acc -> case fv of
      --                                         V v -> M.insert fv v acc
      --                                         FL l -> case l of 
      --                                                     Single loc -> M.insert fv loc acc
      --                                                     SoA _ _ -> let name = mangle (varsInLocVar l)
      --                                                                   in M.insert fv name acc   
      --                                         R r -> case r of 
      --                                                   SingleR v -> M.insert fv v acc
      --                                                   SoARv _ _ -> let name = mangle (varsInRegVar r)
      --                                                                 in M.insert fv name acc
      --                            ) freeVarToVarEnv freeVarsInScope

  freeVarToVarEnv' <- foldrM (\fv acc -> do 
                                            case fv of
                                                V v -> return $ M.insert fv v acc
                                                FL l -> case l of
                                                          Single loc -> return $ M.insert fv loc acc
                                                          SoA _ _ -> do
                                                                      name <- gensym "cursor_ptr"
                                                                      return $ M.insert fv name acc
                                                R r -> case r of
                                                        SingleR v -> return $ M.insert fv v acc
                                                        SoARv _ _ -> do
                                                                      name <- gensym "cursor_ptr"
                                                                      return $ M.insert fv name acc
                                ) freeVarToVarEnv freeVarsInScope

      -- Then the input cursors. Bind an input cursor for every packed argument.
  let inCurBinds = case inLocs of
                     [] -> mkLets []
                     _  ->
                           let projs = concatMap (\(e,t) -> mkInProjs e t) (zip (map VarE funArgs) in_tys)
                               bnds  = zipWith (\loc proj -> let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of 
                                                                                                  Just v -> v 
                                                                                                  Nothing -> error "cursorizeFunDef: unexpected location variable"
                                                                 packed_cursor_ty = case loc of 
                                                                                         Single _ -> CursorTy
                                                                                         SoA _ fields -> CursorArrayTy (1 + length (fields))
                                                               in (var_for_loc, [], packed_cursor_ty, proj)
                                               ) inLocs projs -- [((unwrapLocVar loc),[],CursorTy,proj) | (loc,proj) <- zip inLocs projs]
                           in mkLets bnds

      initTyEnv = M.fromList $ (map (\(a,b) -> (a,MkTy2 (cursorizeInTy (unTy2 b)))) $ zip funArgs in_tys) ++
                               (concatMap (\(LRM l r _) -> let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy l) freeVarToVarEnv') of 
                                                                                                  Just v -> v 
                                                                                                  Nothing -> error "cursorizeFunDef: unexpected location variable"
                                                               packed_cursor_ty = case l of 
                                                                                         Single _ -> CursorTy
                                                                                         SoA _ fields -> CursorArrayTy (1 + length (fields))
                                                               loc_entry = (var_for_loc, MkTy2 packed_cursor_ty)
                                                               var_for_reg = case (M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar $ regionToVar r)) freeVarToVarEnv') of 
                                                                                                  Just v -> v 
                                                                                                  Nothing -> error "cursorizeFunDef: unexpected region variable"
                                                               reg_entry = (var_for_reg, MkTy2 packed_cursor_ty)                                 
                                                             in [loc_entry, reg_entry] 
                                    ) (locVars funTy)
                               ) 

      initTyEnvl = M.fromList $ (map (\(a,b) -> case (unTy2 b) of 
                                                  PackedTy _ l -> (a, Just l)
                                                  _ -> (a, Nothing)
      
                                     ) $ zip funArgs in_tys) ++
                               (concatMap (\(LRM l r _) -> let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy l) freeVarToVarEnv') of 
                                                                                                  Just v -> v 
                                                                                                  Nothing -> error "cursorizeFunDef: unexpected location variable"
                                                               packed_cursor_ty = case l of 
                                                                                         Single _ -> Just l 
                                                                                         SoA _ fields -> Just l
                                                               loc_entry = (var_for_loc, packed_cursor_ty)
                                                               var_for_reg = case (M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar $ regionToVar r)) freeVarToVarEnv') of 
                                                                                                  Just v -> v 
                                                                                                  Nothing -> error "cursorizeFunDef: unexpected region variable"
                                                               reg_entry = (var_for_reg, packed_cursor_ty)                                 
                                                             in [loc_entry, reg_entry] 
                                    ) (locVars funTy)
                               )
           

      funargs = (L.map (\r -> case (M.lookup (fromRegVarToFreeVarsTy r) freeVarToVarEnv') of 
                                            Just v -> v
                                            Nothing -> error "cursorizeFunDef: unexpected region variable"
                       ) regBinds
                ) ++ (L.map (\b -> case (M.lookup (fromLocVarToFreeVarsTy b) freeVarToVarEnv') of 
                                            Just v -> v
                                            Nothing -> error "cursorizeFunDef: unexpected location variable"
                       ) outCurBinds) ++   (L.map (\v -> case (M.lookup (fromVarToFreeVarsTy v) freeVarToVarEnv') of 
                                            Just v -> v
                                            Nothing -> error "cursorizeFunDef: unexpected variable"
                       ) funArgs)
  
  {- Get the regions out before hand, these can be eliminated later on -}
  
  bod <- if hasPacked (unTy2 out_ty)
         then fromDi <$> cursorizePackedExp freeVarToVarEnv' initTyEnvl ddefs fundefs M.empty initTyEnv M.empty funBody
         else cursorizeExp freeVarToVarEnv' initTyEnvl ddefs fundefs M.empty initTyEnv M.empty funBody
  let bod' = inCurBinds bod
      fn = FunDef funName funargs funTy' bod' funMeta
  dbgTrace (minChatLvl) "Print in cursorizeFunDef: " dbgTrace (minChatLvl) (sdoc (initTyEnv, locVars funTy)) dbgTrace (minChatLvl) "End cursorizeFunDef\n" return fn

  where
    -- | The only difference between this and L3.cursorizeTy is that here,
    --   packed types are replaced by a single CursorTy instead of
    --   a tuple (CursorTy,CursorTy). This is because only `start` cursors are
    --   passed in for packed function arguments.
    {- Removing the polymorphism, since this function is local to cursorize and all code before cursorize uses LocVar -}
    cursorizeInTy :: UrTy LocVar -> UrTy b
    cursorizeInTy ty =
      case ty of
        IntTy     -> IntTy
        CharTy    -> CharTy
        FloatTy   -> FloatTy
        SymTy     -> SymTy
        BoolTy    -> BoolTy
        ProdTy ls -> ProdTy $ L.map cursorizeInTy ls
        SymDictTy ar _ty -> SymDictTy ar CursorTy
        PDictTy k v -> PDictTy (cursorizeInTy k) (cursorizeInTy v)
        PackedTy _ l    -> case l of 
                             Single _ -> CursorTy
                             SoA _ fieldLocs -> CursorArrayTy (1 + (length fieldLocs))
        VectorTy el_ty -> VectorTy $ cursorizeInTy el_ty
        ListTy el_ty -> ListTy $ cursorizeInTy el_ty
        PtrTy -> PtrTy
        CursorTy  -> CursorTy
        CursorArrayTy size -> CursorArrayTy size
        ArenaTy   -> ArenaTy
        SymSetTy  -> SymSetTy
        SymHashTy -> SymHashTy
        IntHashTy -> IntHashTy

{-

Build projections for packed values in the input type
This is used to create bindings for input location variables.

    >>> mkInProjs e (PackedTy "T" "l")
    [VarE (Var "funArg")]

    >>> mkInProjs e (ProdTy [IntTy,PackedTy "T" "l"])
    [ProjE 1 VarE (Var "funArg")]

    >>> mkInProje e (ProdTy [ProdTy [PackedTy "T" "l", PackedTy "T" "l"], IntTy])
    [ProjE 0 ProjE 0 e, ProjE 1 ProjE 0 e]

    >>> mkInProje e (ProdTy [PackedTy "T" "l",
                             IntTy,
                             ProdTy [PackedTy "T" "l",
                                     ProdTy [PackedTy "T" "l", PackedTy "T" "l"]]])
    [ProjE 0 e,ProjE 0 ProjE 2 e,ProjE 0 ProjE 1 ProjE 2 e,ProjE 1 ProjE 1 ProjE 2 e]

-}
    mkInProjs :: Exp3 -> Ty2 -> [Exp3]
    mkInProjs e0 ty0 = go [] e0 ty0
     where
       go :: [Exp3] -> Exp3 -> Ty2 -> [Exp3]
       go acc e ty =
         case unTy2 ty of
           PackedTy{} -> acc ++ [e]
           ProdTy tys -> L.foldl (\acc2 (ty',n) -> go acc2 (mkProj n e) ty')
                                 acc (zip (map MkTy2 tys) [0..])
           _ -> acc

    cursorizeArrowTy :: Bool -> ArrowTy2 Ty2 -> ([Ty3] , Ty3)
    cursorizeArrowTy useSoA ty@ArrowTy2{arrIns,arrOut,locVars,locRets} =
      let
          -- Regions corresponding to ouput cursors. (See [Threading regions])
          numOutRegs = length (outRegVars ty)
          --outRegs = L.map (\_ -> CursorTy) [1..numOutRegs]

          outRegs = L.map (\r -> case r of
                                   SingleR v -> CursorTy
                                   SoARv dcr frs -> CursorArrayTy (1 + length frs)
                          ) (outRegVars ty)




          -- Adding additional outputs corresponding to end-of-input-value witnesses
          -- We've already computed additional location return value in RouteEnds
          -- ret_curs = L.map (\_ -> CursorTy) locRets

          ret_curs = L.map (\lret -> case lret of
                                          EndOf (LRM l _ _) -> case l of 
                                                                  Single _ -> CursorTy 
                                                                  SoA dcl flocs -> CursorArrayTy (1 + length flocs)
                                  
                           ) locRets

          out_curs = inRegs ++ outRegs ++ ret_curs
          out_ty = case out_curs of
                     [] -> unTy2 arrOut
                     _  -> ProdTy $ out_curs ++ [unTy2 arrOut]

          -- Packed types in the output then become end-cursors for those same destinations.
          newOut = mapPacked (\var loc -> case loc of 
                                               Single _  -> ProdTy [CursorTy, CursorTy]
                                               SoA _ fields -> ProdTy [CursorArrayTy (1 + length fields), CursorArrayTy (1 + length fields)]
                           
                           ) out_ty

          newOut' = case newOut of
                      SymDictTy a _ -> SymDictTy a CursorTy
                      _ -> newOut

          -- Adding additional input arguments for the destination cursors to which outputs
          -- are written.
          outCurs   = filter (\(LRM _ _ m) -> m == Output) locVars
          outCurTys = map (\(LRM l _ _) -> case l of 
                                        Single _ -> CursorTy
                                        SoA _ fields -> CursorArrayTy (1 + length (fields))
                          ) outCurs
          inRegs    = map (\r -> case r of 
                                    SingleR _ -> CursorTy
                                    SoARv _ frs -> CursorArrayTy (1 + length frs) 
                          ) (inRegVars ty)
          in_tys    = inRegs ++ outRegs ++ outCurTys ++ (map unTy2 arrIns)

          -- Packed types in the input now become (read-only) cursors.

          newIns = if useSoA 
                   then map (cursorizeInTy) in_tys
                   else map (constPacked CursorTy) in_tys

      in dbgTrace (minChatLvl) "Print in_tys" dbgTrace (minChatLvl) (sdoc (out_ty, in_tys)) dbgTrace (minChatLvl) "End in_tys\n" (map stripTyLocs newIns, stripTyLocs newOut')


-- | Cursorize expressions NOT producing `Packed` values
cursorizeExp :: M.Map FreeVarsTy Var -> TyEnv Var (Maybe LocVar) -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2
             -> PassM Exp3
cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex =
  case ex of
    VarE v    -> return $ VarE v
    LitE n    -> return $ LitE n
    CharE c   -> return $ CharE c
    FloatE n  -> return $ FloatE n
    LitSymE n -> return $ LitSymE n

    AppE{} -> cursorizeAppE freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex

    PrimAppE RequestSizeOf [arg] -> do
      let (VarE v) = arg
      case M.lookup v tenv of
        Nothing -> error $ "cursorizeExp: Unbound variable: " ++ sdoc v
        Just ty -> if isPackedTy (unTy2 ty)
                   then pure $ Ext $ SubPtr (toEndV v) v
                   else pure $ LitE $ fromJust $ sizeOfTy (unTy2 ty)

    PrimAppE pr args -> PrimAppE (toL3Prim pr) <$> mapM go args

    LetE (v,_locs, _ty, (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod -> do
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs 
      cursorizeReadPackedFile freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v path tyc reg ty2 bod

    LetE (_v,_locs,_ty, (MkProdE _ls)) _bod -> do 
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs
      cursorizeProd freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, ty, ProjE{}) _bod | isPackedTy (unTy2 ty) -> do 
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs
      cursorizeProj freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, _ty, SpawnE{}) _bod -> do
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs
      cursorizeSpawn freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, _ty, SyncE) _bod -> do 
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs
      cursorizeSync freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex

    LetE (v,_locs,ty, rhs@(Ext (SSPush _ start _ _))) bod -> do 
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go bod
        Just{}  -> do
          rhs' <- go rhs
          bod' <- go bod
          let ty' = cursorizeTy (unTy2 ty)
          return $ LetE (v,[],ty',rhs') bod'

    LetE (v,_locs,ty, rhs@(Ext (SSPop _ start _))) bod ->
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go bod
        Just{}  -> do
          rhs' <- go rhs
          bod' <- go bod
          let ty' = cursorizeTy (unTy2 ty)
          return $ LetE (v,[],ty',rhs') bod'

    -- LetE bnd@(v, _locs, ty, rhs) bod -> case rhs of 
    --   Ext (BoundsCheck i bound cur) -> do 
    --     let bound_loc = toLocVar bound
    --     let bound_var = case (M.lookup (fromLocVarToFreeVarsTy bound_loc) freeVarToVarEnv) of 
    --                                       Just v -> v 
    --                                       Nothing -> error $ "cursorizeExp: BoundsCheck: unexpected location variable" ++ sdoc bound_loc
    --     let cur_loc = toLocVar cur
    --     let cur_var = case (M.lookup (fromLocVarToFreeVarsTy cur_loc) freeVarToVarEnv) of 
    --                                      Just v -> v 
    --                                      Nothing -> error $ "cursorizeExp: BoundsCheck: unexpected location variable" ++ sdoc cur_loc 
    --     exp' <- return $Ext $ L3.BoundsCheck i bound_var cur_var
    --     --exp' <- if isBound cur_var tenv
    --     --       then return $ Ext $ L3.BoundsCheck i bound_var cur_var
    --     --       else do 
    --     --            let denv' = M.insertWith (++) (cur_loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
    --     --         return $ Ext $ L3.BoundsCheck i bound_var cur_var --Left$ M.insertWith (++) ((toLocVar) loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
    --     return exp'
    --   _ -> cursorizeLet freeVarToVarEnv False ddfs fundefs denv tenv senv bnd bod

    LetE bnd@(_,_locs,_, _) bod -> do
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs
      cursorizeLet freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv bnd bod

    IfE a b c  -> IfE <$> go a <*> go b <*> go c

    MkProdE ls -> MkProdE <$> mapM go ls

    ProjE i e  -> ProjE i <$> go e

    -- Eg. leftmost
    CaseE scrt brs -> do
      -- ASSUMPTION: scrt is flat
      freeVarToVarEnv' <- foldrM (\(dcon,vlocs,rhs) acc -> do
                                                           case vlocs of
                                                             [] -> return acc
                                                             _ -> do
                                                                  acc' <- foldrM (\(v, l) acc'' -> do 
                                                                                                   case (toLocVar l) of 
                                                                                                      Single l' -> return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) l' acc''
                                                                                                      SoA _ _ -> do 
                                                                                                                 if M.member (fromLocVarToFreeVarsTy (toLocVar l)) acc''
                                                                                                                 then return acc''
                                                                                                                 else do 
                                                                                                                  name <- gensym "cursor_ptr"
                                                                                                                  return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) name acc''
                                                                                 ) acc vlocs
                                                                  return acc'


                                 ) freeVarToVarEnv brs
      let (VarE  v) = scrt
      let ty_of_scrut = case (M.lookup v tenv) of 
                            Just (MkTy2 ty) -> ty
                            Nothing -> error "unpackDataCon: unexpected location variable"
      dcon_var <- gensym "dcon"
      {-VS: TODO: get location of scrutinee, send it to unpack data con. Get the L2 location!!!-}
      let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
      let dcon_let_bind = mkLets dcon_let
      case ty_of_scrut of 
            CursorTy -> CaseE (VarE $ v) <$>
                            mapM (unpackDataCon dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv False v) brs
            CursorArrayTy{} -> dcon_let_bind <$> CaseE (VarE $ dcon_var) <$>
                                  mapM (unpackDataCon dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv False v) brs
            _ -> CaseE (VarE $ v) <$>
                            mapM (unpackDataCon dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv False v) brs
      

    DataConE _ _ _ -> error $ "cursorizeExp: Should not have encountered DataConE if type is not packed: "++ndoc ex

    TimeIt e ty b -> TimeIt <$> go e <*> pure (stripTyLocs (unTy2 ty)) <*> pure b

    WithArenaE v e -> do
      e' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv (M.insert v (MkTy2 ArenaTy) tenv) senv e
      return $ WithArenaE v e'

    SpawnE{} -> error "cursorizeExp: Unbound SpawnE"
    SyncE{}  -> error "cursorizeExp: Unbound SyncE"

    -- Eg. leftmost
    Ext ext ->
      case ext of
        AddFixed v i -> return $ Ext $ L3.AddCursor v (L3.LitE i)
        RetE locs v ->
          case locs of
              [] -> return (VarE v)
              _  -> return $ L3.MkProdE $ (map (\loc -> let loc_to_free_var = fromLocArgToFreeVarsTy loc
                                                            locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv) of 
                                                                            Just v -> v 
                                                                            Nothing -> case (toLocVar loc) of 
                                                                                            Single lvarr -> lvarr
                                                                                            SoA _ _ ->  error "cursorizeExp: LetLocE: unexpected location variable"
                                                          in VarE locs_variable
                                               ) locs) ++ [VarE v]

        StartOfPkdCursor cur -> return (VarE cur)

        TagCursor a b -> return $ Ext $ L3.TagCursor a b

        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let ty2_of_loc = case loc of 
                             Single l -> CursorTy
                             SoA _ fields -> CursorArrayTy (1 + length fields)
          let ty3_of_loc :: Ty3 = case loc of 
                                    Single l -> CursorTy
                                    SoA _ fields -> CursorArrayTy (1 + length fields) 
          freeVarToVarEnv' <- do 
                              case loc of 
                                    Single l -> if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return freeVarToVarEnv
                                                else return $ M.insert (fromLocVarToFreeVarsTy loc) l freeVarToVarEnv
                                    SoA _ _ -> if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return $ freeVarToVarEnv
                                                else do
                                                  name <- gensym "cursor_ptr"
                                                  return $ M.insert (fromLocVarToFreeVarsTy loc) name freeVarToVarEnv
          let locs_variable = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of 
                                Just v -> v 
                                Nothing -> case loc of 
                                                Single lvarrr -> lvarrr
                                                SoA _ _ ->  error "cursorizeExp: LetLocE: unexpected location variable"
          let    rhs_either = cursorizeLocExp freeVarToVarEnv' denv tenv senv loc rhs
          let    (bnds,tenv') = case M.lookup (fromLocVarToFreeVarsTy loc) denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v,MkTy2 CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            -- Check if the location is already bound before. If so, don't
            -- create a duplicate binding. This only happens when we
            -- have indirection _and_ a end-witness for a particular value.
            -- For example, consider a pattern like
            --     (Node^ [(ind_y2, loc_ind_y2), (x1, loc_x1), (y2, loc_y2)] BODY)
            --
            -- occuring in a function like sum-tree.
            --
            -- While unpacking this constructor, we bind y2 to ind_y2.
            -- But since sum-tree traverses it's input, we will enconter
            -- (y2 = end_x1) sometime later in the AST (due to RouteEnds).
            -- We just ignore the second binding for now.
            --
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of 
                                Just v -> v 
                                Nothing -> case loc of 
                                              Single lvarrr -> lvarrr
                                              SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              case rhs of
                FromEndLE{} ->
                  if isBound locs_var tenv
                  then cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv' bod
                  -- Discharge bindings that were waiting on 'loc'.
                  else mkLets (bnds' ++ [(locs_var,[],ty3_of_loc,rhs')] ++ bnds) <$>
                         cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv' bod
                -- Discharge bindings that were waiting on 'loc'.
                _ -> mkLets (bnds' ++ [(locs_var,[],ty3_of_loc,rhs')] ++ bnds) <$>
                       cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv bod
            Left denv' -> cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod

        -- Exactly same as cursorizePackedExp
        LetRegionE reg sz _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv False reg sz
          mkLets (region_lets) <$> cursorizeExp freeVarToVarEnv' lenv  ddfs fundefs denv tenv senv bod

        LetParRegionE reg sz _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv True reg sz
          mkLets (region_lets) <$> cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv tenv senv bod
        
        {- VS: TODO: variables are not in env-}
        {- TODO: End of reg needs fixing is broken -}
        BoundsCheck i bound cur -> do 
                                   let bound_loc = toLocVar bound
                                   let bound_reg = fromLocVarToRegVar bound_loc
                                   let bound_var = case (M.lookup (fromRegVarToFreeVarsTy bound_reg) freeVarToVarEnv) of 
                                                     Just v -> v 
                                                     Nothing -> case bound_reg of 
                                                                     SingleR vr -> vr
                                                                     SoARv _ _ -> error $ "cursorizeExp: BoundsCheck: unexpected region variable " ++ sdoc bound_loc ++ " " ++ show freeVarToVarEnv
                                   let cur_loc = toLocVar cur
                                   let cur_var = case (M.lookup (fromLocVarToFreeVarsTy cur_loc) freeVarToVarEnv) of 
                                                     Just v -> v 
                                                     Nothing -> error $ "cursorizeExp: BoundsCheck: unexpected location variable" ++ sdoc cur_loc ++ " " ++ show freeVarToVarEnv
                                   exp' <- return $ Ext $ L3.BoundsCheck i bound_var cur_var
                                   --exp' <- if isBound cur_var tenv
                                   --       then return $ Ext $ L3.BoundsCheck i bound_var cur_var
                                   --       else do 
                                   --            let denv' = M.insertWith (++) (cur_loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
                                   --         return $ Ext $ L3.BoundsCheck i bound_var cur_var --Left$ M.insertWith (++) ((toLocVar) loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
                                   return exp'

        FromEndE{} -> error $ "cursorizeExp: TODO FromEndE" ++ sdoc ext

        IndirectionE{} -> error $ "cursorizeExp: Unexpected IndirectionE"

        GetCilkWorkerNum -> return $ Ext $ L3.GetCilkWorkerNum

        LetAvail vs bod  -> Ext <$> L3.LetAvail vs <$> go bod

        AllocateTagHere v tycon -> do 
                                   let variable_name = case (M.lookup (fromLocVarToFreeVarsTy v) freeVarToVarEnv) of 
                                                            Just v -> v 
                                                            Nothing -> error "cursorizeExp: AllocateTagHere: unexpected location variable"
                                   pure $ Ext $ L3.AllocateTagHere (variable_name) tycon

        AllocateScalarsHere v -> do 
                                 let variable_name = case (M.lookup (fromLocVarToFreeVarsTy v) freeVarToVarEnv) of 
                                                            Just v -> v 
                                                            Nothing -> error "cursorizeExp: AllocateTagHere: unexpected location variable"
                                 pure $ Ext $ L3.AllocateScalarsHere (variable_name)

        SSPush a b c d -> pure $ Ext $ L3.SSPush a (unwrapLocVar b) (unwrapLocVar c) d
        SSPop a b c -> pure $ Ext $ L3.SSPop a (unwrapLocVar b) (unwrapLocVar c)

        {-VS: TODO: This needs to be fixed to produce the correct L3 expression. See above. -}      
        {- Right now i just skip the let region, just recurse on the body-}              
        LetRegE loc rhs bod -> do
          --let loc = fromRegVarToLocVar reg_var
          let ty_of_loc = case loc of 
                            SingleR _ -> CursorTy
                            SoARv _ flds -> CursorArrayTy (1 + length flds)
          freeVarToVarEnv' <- do 
                              case loc of 
                                    SingleR l -> if M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return freeVarToVarEnv
                                                else return $ M.insert (fromRegVarToFreeVarsTy loc) l freeVarToVarEnv
                                    SoARv _ _ -> if M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return $ freeVarToVarEnv
                                                else do
                                                  name <- gensym "cursor_ptr"
                                                  return $ M.insert (fromRegVarToFreeVarsTy loc) name freeVarToVarEnv
          let rhs_either = cursorizeRegExp freeVarToVarEnv' denv tenv senv loc rhs
              (bnds,tenv') = case M.lookup (fromRegVarToFreeVarsTy loc) denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v, MkTy2 CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromRegVarToFreeVarsTy loc) freeVarToVarEnv') of 
                                Just v -> v 
                                Nothing -> case loc of 
                                                SingleR lvarrr -> lvarrr 
                                                SoARv _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              case rhs of
                -- Discharge bindings that were waiting on 'loc'. 
                _ ->  mkLets (bnds' ++ [(locs_var,[],ty_of_loc,rhs')] ++ bnds) <$>
                       cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 CursorTy) tenv''') senv' bod
                       -- cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv' bod
            Left denv' -> (mkLets bnds) <$>
                            cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod
          -- case reg_var of
          -- SingleR v -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod
          -- SoARv dv _ -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod

        _ -> error $ "Unpexected Expression: " ++ show ext

    MapE{} -> error $ "TODO: cursorizeExp MapE"
    FoldE{} -> error $ "TODO: cursorizeExp FoldE"

  where
    go = cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv



insertRegInVarEnv :: RegVar -> M.Map FreeVarsTy Var -> PassM (M.Map FreeVarsTy Var)
insertRegInVarEnv reg_var env = do 
                                    case reg_var of 
                                          SingleR l -> if M.member (fromRegVarToFreeVarsTy reg_var) env
                                                        then return env
                                                        else return $ M.insert (fromRegVarToFreeVarsTy reg_var) l env
                                          SoARv _ _ -> if M.member (fromRegVarToFreeVarsTy reg_var) env
                                                        then return $ env
                                                        else do
                                                          name <- gensym "reg_cursor_ptr"
                                                          return $ M.insert (fromRegVarToFreeVarsTy reg_var) name env

insertLocInVarEnv :: LocVar -> M.Map FreeVarsTy Var -> PassM (M.Map FreeVarsTy Var)
insertLocInVarEnv loc env = do 
                                case loc of 
                                      Single l -> if M.member (fromLocVarToFreeVarsTy loc) env
                                                  then return env
                                                  else return $ M.insert (fromLocVarToFreeVarsTy loc) l env
                                      SoA _ _ -> if M.member (fromLocVarToFreeVarsTy loc) env
                                                  then return $ env
                                                  else do
                                                    name <- gensym "loc_cursor_ptr"
                                                    return $ M.insert (fromLocVarToFreeVarsTy loc) name env

-- Cursorize expressions producing `Packed` values
cursorizePackedExp :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2
                   -> PassM (DiExp Exp3)
cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex =
  case ex of
    -- Here the allocation has already been performed:
    -- To follow the calling convention, we are reponsible for tagging on the
    -- end here:
    VarE v -> do
      let ty = case M.lookup v tenv of
                 Just t -> t
                 Nothing -> error $ sdoc v ++ " not found."
      if isPackedTy (unTy2 ty)
      then return $ mkDi (VarE v) [ VarE (toEndV v) ]
      else return $ dl $ VarE v

    LitE _n    -> error $ "Shouldn't encounter LitE in packed context:" ++ sdoc ex
    CharE _n   -> error $ "Shouldn't encounter CharE in packed context:" ++ sdoc ex
    FloatE{}   -> error $ "Shouldn't encounter FloatE in packed context:" ++ sdoc ex
    LitSymE _n -> error $ "Shouldn't encounter LitSymE in packed context:" ++ sdoc ex

    AppE{} -> dl <$> cursorizeAppE freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex

    -- DictLookup returns a packed value bound to a free location.
    -- PrimAppE (DictLookupP (PackedTy _ ploc)) vs ->
    --     do vs' <- forM vs $ \v -> cursorizeExp ddfs fundefs denv tenv v
    --        return $ mkDi (PrimAppE (DictLookupP CursorTy) vs') [ Ext NullCursor ]

    PrimAppE _ _ -> error $ "cursorizePackedExp: unexpected PrimAppE in packed context:" ++ sdoc ex

    -- The only (other) primitive that returns packed data is ReadPackedFile:
    -- This is simpler than TimeIt below.  While it's out-of-line,
    -- it doesn't need memory allocation (NewBuffer/ScopedBuffer).
    -- This is more like the witness case below.
    LetE (v,_locs, _ty, (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod ->
       Di <$> cursorizeReadPackedFile freeVarToVarEnv lenv ddfs fundefs denv tenv senv True v path tyc reg ty2 bod

    LetE (v,_locs,_ty, (PrimAppE (DictLookupP (MkTy2 (PackedTy _ ploc))) vs)) bod ->
        do vs' <- forM vs $ \w -> cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv w
           let bnd = mkLets [((unwrapLocVar ploc), [], CursorTy, (PrimAppE (DictLookupP CursorTy) vs'))
                            ,(v, [], CursorTy, VarE (unwrapLocVar ploc))]
               tenv' = M.insert (unwrapLocVar ploc) (MkTy2 CursorTy) $ M.insert v (MkTy2 CursorTy) tenv
           onDi bnd <$> go freeVarToVarEnv tenv' senv bod

    LetE (_v,_locs,_ty, (MkProdE _ls)) _bod ->
      dl <$> cursorizeProd freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex

    LetE (_v,_locs,ty, ProjE{}) _bod | isPackedTy (unTy2 ty) ->
      dl <$> cursorizeProj freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex


    MkProdE ls -> do
      let tys = L.map (gRecoverType ddfs (Env2 tenv M.empty)) ls
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy (unTy2 ty) -> fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
                  _ -> cursorizeExp  freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
      let rhs' = MkProdE es
      return $ Di rhs'

    -- Not sure if we need to replicate all the checks from Cursorize1
    ProjE i e -> dl <$> ProjE i <$> fromDi <$> go freeVarToVarEnv tenv senv e

    LetE (_v,_locs, _ty, SpawnE{}) _bod ->
      dl <$> cursorizeSpawn freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, _ty, SyncE) _bod ->
      dl <$> cursorizeSync freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex

    LetE (v,_locs,ty, rhs@(Ext (SSPush _ start _ _))) bod ->
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go freeVarToVarEnv tenv senv bod
        Just{}  -> do
          rhs' <- go freeVarToVarEnv tenv senv rhs
          let ty' = cursorizeTy (unTy2 ty)
          bod' <- go freeVarToVarEnv (M.insert v ty tenv) senv bod
          return $ Di (LetE (v,[], ty', fromDi rhs') (fromDi bod'))

    LetE (v,_locs,ty, rhs@(Ext (SSPop _ start _))) bod ->
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go freeVarToVarEnv tenv senv bod
        Just{}  -> do
          rhs' <- go freeVarToVarEnv tenv senv rhs
          let ty' = cursorizeTy (unTy2 ty)
          bod' <- go freeVarToVarEnv (M.insert v ty tenv) senv bod
          return $ Di (LetE (v,[],ty', fromDi rhs') (fromDi bod'))

    LetE bnd@(_,_locs,_, _) bod -> do
      freeVarToVarEnv' <- foldrM (\loc env -> case loc of 
                                                   EndOfReg r _ er -> do
                                                                      env' <- insertRegInVarEnv r env 
                                                                      env'' <- insertRegInVarEnv er env'
                                                                      return env''
                                                   EndWitness lrem loc -> do
                                                                      env' <- insertLocInVarEnv loc env
                                                                      env'' <- insertLocInVarEnv (lremLoc lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                                                                      env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                                                                      return env''''
                                                   Loc lrem -> do
                                                                      env' <- insertLocInVarEnv (lremLoc lrem) env
                                                                      env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                                                                      env''' <- insertRegInVarEnv (lremReg lrem) env''
                                                                      return env'''
                                                   Reg r _ -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                                   EndOfReg_Tagged r -> do
                                                                      env' <- insertRegInVarEnv r env
                                                                      return env'
                                 ) freeVarToVarEnv _locs
      dl <$> cursorizeLet freeVarToVarEnv' lenv True ddfs fundefs denv tenv senv bnd bod

    -- Here we route the dest cursor to both braches.  We switch
    -- back to the other mode for the (non-packed) test condition.
    IfE a b c -> do
      Di b' <- go freeVarToVarEnv tenv senv b
      Di c' <- go freeVarToVarEnv tenv senv c
      a'    <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv a
      return $ Di $ IfE a' b' c'

    -- A case expression is eventually transformed into a ReadTag + switch stmt.
    -- We first retrieve the cursor referred to by the scrutinee, and unpack
    -- the first bound variable 1 byte after that cursor. Thats all we need to do
    -- here, because we've already computed other locations in InferLocations and
    -- RouteEnds
    CaseE scrt brs -> do
      -- ASSUMPTION: scrutinee is always flat
      let (VarE v) = scrt
      
      freeVarToVarEnv' <- foldrM (\(dcon,vlocs,rhs) acc -> do
                                                           case vlocs of
                                                             [] -> return acc
                                                             _ -> do
                                                                  acc' <- foldrM (\(v, l) acc'' -> do 
                                                                                                   case (toLocVar l) of 
                                                                                                      Single l' -> return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) l' acc''
                                                                                                      SoA _ _ -> do 
                                                                                                                 if M.member (fromLocVarToFreeVarsTy (toLocVar l)) acc''
                                                                                                                 then return acc''
                                                                                                                 else do 
                                                                                                                  name <- gensym "cursor_ptr"
                                                                                                                  return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) name acc''
                                                                                 ) acc vlocs
                                                                  return acc'


                                 ) freeVarToVarEnv brs
      let ty_of_scrut = case (M.lookup v tenv) of 
                            Just (MkTy2 ty) -> ty
                            Nothing -> error "unpackDataCon: unexpected location variable"
      dcon_var <- gensym "dcon"
      let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
      let dcon_let_bind = mkLets dcon_let 
      case ty_of_scrut of 
        CursorTy -> dl <$>
                      CaseE (VarE $ v) <$>
                        mapM (unpackDataCon dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v) brs
        CursorArrayTy{} ->  dl <$> dcon_let_bind <$>
                              CaseE (VarE $ dcon_var) <$>
                                mapM (unpackDataCon dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v) brs
        _ -> dl <$>
                      CaseE (VarE $ v) <$>
                        mapM (unpackDataCon dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v) brs                  
      

    DataConE slocarg dcon args -> do
      if (not (isSoALoc (toLocVar slocarg)))
      then do
        let sloc_loc = toLocVar slocarg
            sloc = case (M.lookup (fromLocVarToFreeVarsTy sloc_loc) freeVarToVarEnv) of 
                           Just v -> v 
                           Nothing -> error $ "cursorizeExp(988): DataConE: unexpected location variable" ++ "(" ++ show sloc_loc ++ ")" ++ show freeVarToVarEnv
            -- Return (start,end) cursors
            -- The final return value lives at the position of the out cursors:
            go2 :: Bool -> Var -> [(Exp2, Ty2)] -> PassM Exp3
            go2 marker_added d [] =
              if not (marker_added)
              then do
                end_scalars_alloc <- gensym "end_scalars_alloc"
                return (LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation sloc)
                             (MkProdE [VarE (sloc), VarE d]))
              else return (MkProdE [VarE (sloc), VarE d])

            go2 marker_added d ((rnd, (MkTy2 ty)):rst) = do
              d' <- gensym "writecur"
              case ty of
                _ | isPackedTy ty -> do

                  rnd' <- go freeVarToVarEnv tenv senv rnd
                  end_scalars_alloc <- gensym "end_scalars_alloc"
                  (if not marker_added
                    then LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation (sloc))
                    else id) <$>
                    LetE (d',[], CursorTy, projEnds rnd') <$>
                    go2 True d' rst

                -- Int, Float, Sym, or Bool
                _ | isScalarTy ty -> do
                  rnd' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                  LetE (d',[], CursorTy, Ext $ WriteScalar (mkScalar ty) d rnd') <$>
                    go2 marker_added d' rst

                -- Write a pointer to a vector
                VectorTy el_ty -> do
                  rnd' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                  LetE (d',[], CursorTy, Ext $ WriteVector d rnd' (stripTyLocs el_ty)) <$>
                    go2 marker_added d' rst

                -- Write a pointer to a vector
                ListTy el_ty -> do
                  rnd' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                  LetE (d',[], CursorTy, Ext $ WriteList d rnd' (stripTyLocs el_ty)) <$>
                    go2 marker_added d' rst

                -- shortcut pointer
                CursorTy -> do
                  rnd' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                  LetE (d',[], CursorTy, Ext $ WriteTaggedCursor d rnd') <$>
                    go2 marker_added d' rst
                _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty

        writetag <- gensym "writetag"
        after_tag <- gensym "after_tag"
        start_tag_alloc <- gensym "start_tag_alloc"
        end_tag_alloc <- gensym "end_tag_alloc"
        start_scalars_alloc <- gensym "start_scalars_alloc"
        dl <$>
          LetE (start_tag_alloc,[],ProdTy [], Ext $ StartTagAllocation (sloc)) <$>
          LetE (writetag,[], CursorTy, Ext $ WriteTag dcon (sloc)) <$>
          LetE (end_tag_alloc,[],ProdTy [], Ext $ EndTagAllocation (sloc)) <$>
          LetE (start_scalars_alloc,[],ProdTy [], Ext $ StartScalarsAllocation (sloc)) <$>
          LetE (after_tag,[], CursorTy, Ext $ AddCursor (sloc) (L3.LitE 1)) <$>
            go2 False after_tag (zip args (lookupDataCon ddfs dcon))
      else do
        let sloc_loc = toLocVar slocarg
            dcon_loc = getDconLoc sloc_loc 
            field_locs = getAllFieldLocsSoA sloc_loc
            sloc = case (M.lookup (fromLocVarToFreeVarsTy sloc_loc) freeVarToVarEnv) of 
                           Just v -> v 
                           Nothing -> error $ "cursorizeExp(1056): DataConE: unexpected location variable" ++ "(" ++ show sloc_loc ++ ")" ++ show freeVarToVarEnv
            sloc_dcon = case (M.lookup (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv) of 
                           Just v -> v 
                           Nothing -> case dcon_loc of
                                            Single l -> l
                                            _ -> error $ "cursorizeExp(1059): DataConE: unexpected dcon location variable" ++ "(" ++ show (dcon, dcon_loc) ++ ")" ++ show freeVarToVarEnv
            -- Return (start,end) cursors
            -- The final return value lives at the position of the out cursors:
            -- go2 :: Bool -> Var -> [(Exp2, Ty2)] -> PassM Exp3
            -- go2 marker_added d [] =
            --   if not (marker_added)
            --   then do
            --     end_scalars_alloc <- gensym "end_scalars_alloc"
            --     return (LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation sloc)
            --                  (MkProdE [VarE (sloc), VarE d]))
            --   else return (MkProdE [VarE (sloc), VarE d])

            -- go2 marker_added d ((rnd, (MkTy2 ty)):rst) = do
            --   d' <- gensym "writecur"
            --   case ty of
            --     _ | isPackedTy ty -> do

            --       rnd' <- go freeVarToVarEnv tenv senv rnd
            --       end_scalars_alloc <- gensym "end_scalars_alloc"
            --       (if not marker_added
            --         then LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation (sloc))
            --         else id) <$>
            --         LetE (d',[], CursorTy, projEnds rnd') <$>
            --         go2 True d' rst

            --     -- Int, Float, Sym, or Bool
            --     _ | isScalarTy ty -> do
            --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
            --       LetE (d',[], CursorTy, Ext $ WriteScalar (mkScalar ty) d rnd') <$>
            --         go2 marker_added d' rst

            --     -- Write a pointer to a vector
            --     VectorTy el_ty -> do
            --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
            --       LetE (d',[], CursorTy, Ext $ WriteVector d rnd' (stripTyLocs el_ty)) <$>
            --         go2 marker_added d' rst

            --     -- Write a pointer to a vector
            --     ListTy el_ty -> do
            --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
            --       LetE (d',[], CursorTy, Ext $ WriteList d rnd' (stripTyLocs el_ty)) <$>
            --         go2 marker_added d' rst

            --     -- shortcut pointer
            --     CursorTy -> do
            --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
            --       LetE (d',[], CursorTy, Ext $ WriteTaggedCursor d rnd') <$>
            --         go2 marker_added d' rst
            --     _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty 
            
            dummy :: PassM Exp3
            dummy = return $ VarE (sloc)


            go2 :: Bool -> M.Map FreeVarsTy Var -> Var -> Maybe Var -> [((DataCon, Int), LocVar)] -> [((DataCon, Int), Maybe LocVar, (Exp2, Ty2))] -> PassM Exp3
            go2 marker_added fvarenv aft_dloc from_rec_end aft_flocs [] = do
              let curr_soa_loc = sloc
              if not (marker_added)
              then do
                after_soa_loc <- gensym "aft_soa_loc"
                let after_flocs_to_vars = map (\(_, floc) -> case (M.lookup (fromLocVarToFreeVarsTy $ floc) fvarenv) of 
                                                                Just v -> v 
                                                                Nothing -> case floc of 
                                                                             Single l -> l  
                                                                             _ -> error $ "cursorizeExp (1123): DataConE: unexpected location variable" ++ "(" ++ show (dcon, floc) ++ ")" ++ show fvarenv
                                            ) aft_flocs
                let makeCurArr = Ext $ MakeCursorArray (1 + length (aft_flocs)) ([aft_dloc] ++ after_flocs_to_vars)
                let let_mk_cur_arr = LetE (after_soa_loc, [], CursorArrayTy (1 + length (aft_flocs)), makeCurArr)
                end_scalars_alloc <- gensym "end_scalars_alloc" 
                return (let_mk_cur_arr $ LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation (curr_soa_loc))
                             (MkProdE [VarE (curr_soa_loc), VarE (after_soa_loc)]))
              else do 
                let rec_end_var = case from_rec_end of 
                                          Just v -> v 
                                          Nothing -> error "cursorizeExp: go2: expected a recursive end."
                return (MkProdE [VarE (curr_soa_loc), VarE (rec_end_var)])

            go2 marker_added fvarenv aft_dloc from_rec_end aft_flocs (((dcon, index), floc, (rnd, (MkTy2 ty))):rst) = do
              d' <- gensym "writecur"
              case ty of
                PackedTy _ l -> do
                  let cur_ty = case l of 
                              Single _ -> CursorTy
                              SoA _ fields -> CursorArrayTy (1 + length (fields))
                  rnd' <- go freeVarToVarEnv tenv senv rnd
                  end_scalars_alloc <- gensym "end_scalars_alloc"
                  (if not marker_added
                    then LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation (sloc))
                    else id) <$>
                    LetE (d', [], cur_ty, projEnds rnd') <$>
                    go2 True fvarenv aft_dloc (Just d') aft_flocs rst

                _ | isScalarTy ty -> do
                  rnd' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                  -- get the location variable where the scalar must be written
                  let floc_loc = case floc of 
                                       Just l -> l 
                                       Nothing -> error "cursorizeExp: DataConE: expected a location for scalar buffer"
                  let floc_var = case (M.lookup (fromLocVarToFreeVarsTy $ floc_loc) fvarenv) of 
                                        Just v -> v 
                                        Nothing -> case floc_loc of 
                                                        Single l -> l 
                                                        SoA _ _ -> error $ "cursorizePackedExp: DataConE(" ++ show dcon ++ ") : unexpected location variable " ++ ":" ++ show floc_loc ++ "\n\n" ++ show fvarenv
                  write_scalars_at <- gensym "write_scalars_at"
                  let let_assign_write_cur = LetE (write_scalars_at, [], CursorTy, (VarE floc_var))
                  {- Update, aft_flocs with the correct location for the scalar field -}
                  {- TODO: Audit aft_flocs'  and fvarenv'-}
                  {- TODO: Check if its fine to use singleLocVar d' here!! -}
                  let aft_flocs' = map (\((d, idx'), l) -> if d == dcon && idx' == index
                                                            then ((d, idx'), singleLocVar d')
                                                            else ((d, idx'), l)
                                       ) aft_flocs
                  let fvarenv' = M.insert (fromLocVarToFreeVarsTy $ singleLocVar $ d') d' fvarenv
                  let_assign_write_cur <$> LetE (d',[], CursorTy, Ext $ WriteScalar (mkScalar ty) write_scalars_at rnd') <$>
                    go2 marker_added fvarenv' aft_dloc from_rec_end aft_flocs' rst

                
                    -- Write a pointer to a vector
                VectorTy el_ty -> do
                  rnd' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                  -- get the location variable where the scalar must be written
                  let floc_loc = case floc of 
                                       Just l -> l 
                                       Nothing -> error "cursorizeExp: DataConE: expected a location for scalar buffer"
                  let floc_var = case (M.lookup (fromLocVarToFreeVarsTy $ floc_loc) fvarenv) of 
                                        Just v -> v 
                                        Nothing -> case floc_loc of 
                                                        Single l -> l 
                                                        SoA _ _ -> error $ "cursorizePackedExp: DataConE(" ++ show dcon ++ ") : unexpected location variable " ++ ":" ++ show floc_loc ++ "\n\n" ++ show fvarenv
                  write_vector_at <- gensym "write_vector_at"
                  let let_assign_write_cur = LetE (write_vector_at, [], CursorTy, (VarE floc_var))
                  {- Update, aft_flocs with the correct location for the scalar field -}
                  {- TODO: Audit aft_flocs'  and fvarenv'-}
                  {- TODO: Check if its fine to use singleLocVar d' here!! -}
                  let aft_flocs' = map (\((d, idx'), l) -> if d == dcon && idx' == index
                                                            then ((d, idx'), singleLocVar d')
                                                            else ((d, idx'), l)
                                       ) aft_flocs
                  let fvarenv' = M.insert (fromLocVarToFreeVarsTy $ singleLocVar $ d') d' fvarenv
                  let_assign_write_cur <$> LetE (d',[], CursorTy, Ext $ WriteVector write_vector_at rnd' (stripTyLocs el_ty)) <$>
                    go2 marker_added fvarenv' aft_dloc from_rec_end aft_flocs' rst

                _ -> error "TODO: Cursorize: cursorizePackedExp: Not implemented!!"

                -- -- Write a pointer to a vector
                -- ListTy el_ty -> do
                --   rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
                --   LetE (d',[], CursorTy, Ext $ WriteList d rnd' (stripTyLocs el_ty)) <$>
                --     go2 marker_added d' rst

                -- -- shortcut pointer
                -- CursorTy -> do
                --   rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
                --   LetE (d',[], CursorTy, Ext $ WriteTaggedCursor d rnd') <$>
                --     go2 marker_added d' rst
                -- _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty 


              
        writetag <- gensym "writetag"
        after_tag <- gensym "after_tag"
        start_tag_alloc <- gensym "start_tag_alloc"
        end_tag_alloc <- gensym "end_tag_alloc"
        start_scalars_alloc <- gensym "start_scalars_alloc"
        let exp_f_tys = zip args (lookupDataCon ddfs dcon)
        -- [((DataCon, Int), Maybe Location, (Exp2, Ty2))]
        let locs_tys = map (\e@(rnd, (MkTy2 ty)) -> let idx = case (L.elemIndex e exp_f_tys) of 
                                                                  Just idx -> idx
                                                                  Nothing -> error "cursorizeExp: DataConE: field not found!"
                                                        key = (dcon, idx)
                                                        loc = L.lookup key field_locs
                                                      in (key, loc, e)
                           ) exp_f_tys
        dl <$>
          LetE (start_tag_alloc,[],ProdTy [], Ext $ StartTagAllocation (sloc)) <$>
          LetE (writetag,[], CursorTy, Ext $ WriteTag dcon (sloc_dcon)) <$>
          LetE (end_tag_alloc,[],ProdTy [], Ext $ EndTagAllocation (sloc)) <$>
          LetE (start_scalars_alloc,[],ProdTy [], Ext $ StartScalarsAllocation (sloc)) <$>
          LetE (after_tag,[], CursorTy, Ext $ AddCursor (sloc_dcon) (L3.LitE 1)) <$>
          go2 False freeVarToVarEnv after_tag Nothing field_locs locs_tys  

          -- go2 :: Bool -> M.Map FreeVarsTy Var -> Var -> [((DataCon, Int), Location, (Exp2, Ty2))] -> [((DataCon, Int), Location, (Exp2, Ty2))] -> PassM Exp3
          -- go2 False after_tag (zip args (lookupDataCon ddfs dcon))
      

    TimeIt e t b -> do
      Di e' <- go freeVarToVarEnv tenv senv e
      return $ Di $ TimeIt e' (cursorizeTy (unTy2 t)) b

    WithArenaE v e -> do
      Di e' <- go freeVarToVarEnv (M.insert v (MkTy2 ArenaTy) tenv) senv e
      return $ Di $ WithArenaE v e'

    SpawnE{} -> error "cursorizePackedExp: Unbound SpawnE"
    SyncE{}  -> error "cursorizePackedExp: Unbound SyncE"

    Ext ext ->
      case ext of
        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          freeVarToVarEnv' <- do 
                              case loc of
                                    Single l -> if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return freeVarToVarEnv
                                                else return $ M.insert (fromLocVarToFreeVarsTy loc) l freeVarToVarEnv
                                    SoA _ _ -> if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return $ freeVarToVarEnv
                                                else do
                                                  name <- gensym "cursor_ptr"
                                                  return $ M.insert (fromLocVarToFreeVarsTy loc) name freeVarToVarEnv
          let rhs_either = dbgTrace (minChatLvl) "Print env" dbgTrace (minChatLvl) (sdoc (freeVarToVarEnv')) dbgTrace (minChatLvl) "End env\n" cursorizeLocExp freeVarToVarEnv' denv tenv senv loc rhs
              (bnds,tenv') = case M.lookup (fromLocVarToFreeVarsTy loc) denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v, MkTy2 CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of 
                                Just v -> v 
                                Nothing -> case loc of 
                                              Single lvarrr -> lvarrr 
                                              SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              let locs_ty3 :: Ty3 = case loc of
                                Single _ -> CursorTy
                                SoA _ fields -> CursorArrayTy (1 + length (fields))
              let locs_ty2 = case loc of
                                Single _ -> CursorTy
                                SoA _ fields -> CursorArrayTy (1 + length (fields))
              case rhs of
                FromEndLE{} ->
                  if isBound locs_var tenv
                  then go freeVarToVarEnv' (M.insert locs_var (MkTy2 locs_ty2) tenv''') senv' bod
                    -- Discharge bindings that were waiting on 'loc'.
                  else onDi (mkLets (bnds' ++ [(locs_var,[],locs_ty3,rhs')] ++ bnds)) <$>
                         go freeVarToVarEnv' (M.insert locs_var (MkTy2 locs_ty2) tenv') senv' bod
                -- Discharge bindings that were waiting on 'loc'. 
                _ -> onDi (mkLets (bnds' ++ [(locs_var,[],locs_ty3,rhs')] ++ bnds)) <$>
                       go freeVarToVarEnv' (M.insert locs_var (MkTy2 locs_ty2) tenv''') senv' bod
            Left denv' -> onDi (mkLets bnds) <$>
                            cursorizePackedExp freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod

        {-VS: TODO: This needs to be fixed to produce the correct L3 expression. See above. -}      
        {- Right now i just skip the let region, just recurse on the body-}              
        LetRegE loc rhs bod -> do
          --let loc = fromRegVarToLocVar reg_var
          let ty_of_loc = case loc of 
                            SingleR _ -> CursorTy
                            SoARv _ flds -> CursorArrayTy (1 + length flds)
          freeVarToVarEnv' <- do 
                              case loc of 
                                    SingleR l -> if M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return freeVarToVarEnv
                                                else return $ M.insert (fromRegVarToFreeVarsTy loc) l freeVarToVarEnv
                                    SoARv _ _ -> if M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv
                                                then return $ freeVarToVarEnv
                                                else do
                                                  name <- gensym "cursor_ptr"
                                                  return $ M.insert (fromRegVarToFreeVarsTy loc) name freeVarToVarEnv
          let rhs_either = cursorizeRegExp freeVarToVarEnv' denv tenv senv loc rhs
              (bnds,tenv') = case M.lookup (fromRegVarToFreeVarsTy loc) denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v, MkTy2 CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromRegVarToFreeVarsTy loc) freeVarToVarEnv') of 
                                Just v -> v 
                                Nothing -> case loc of 
                                                SingleR lvarrr -> lvarrr 
                                                SoARv _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              case rhs of
                -- Discharge bindings that were waiting on 'loc'. 
                _ -> onDi (mkLets (bnds' ++ [(locs_var,[],ty_of_loc,rhs')] ++ bnds)) <$>
                       go freeVarToVarEnv' (M.insert locs_var (MkTy2 CursorTy) tenv''') senv' bod
            Left denv' -> onDi (mkLets bnds) <$>
                            cursorizePackedExp freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod
          -- case reg_var of
          -- SingleR v -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod
          -- SoARv dv _ -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod

        StartOfPkdCursor cur -> return $ dl $ VarE cur

        TagCursor a b -> return $ dl $ Ext $ L3.TagCursor a b

        -- ASSUMPTION: RetE forms are inserted at the tail position of functions,
        -- and we safely just return ends-witnesses & ends of the dilated expressions
        RetE locs v -> do
          v' <- go freeVarToVarEnv tenv senv (VarE v)
          case locs of
            []    -> return v'
            [loc] -> do
                     let loc_to_free_var = fromLocArgToFreeVarsTy loc
                     let locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv) of 
                                          Just v -> v 
                                          Nothing -> case (toLocVar loc) of
                                                              Single lvarr -> lvarr
                                                              SoA _ _ ->  error "cursorizeExp: LetLocE: unexpected location variable"
              
                     pure $ mkDi (VarE (locs_variable)) [ fromDi v' ]
            _ -> return $ Di $ L3.MkProdE $ L.foldr (\loc acc -> let loc_to_free_var = fromLocArgToFreeVarsTy loc
                                                                     locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv) of 
                                                                                      Just v -> v 
                                                                                      Nothing -> case (toLocVar loc) of
                                                                                                      Single lvarr -> lvarr 
                                                                                                      SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
                                                                  in (VarE (locs_variable)):acc
                                                    ) [fromDi v'] locs

        LetRegionE r sz _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv False r sz
          onDi (mkLets (region_lets)) <$> go freeVarToVarEnv' tenv senv bod

        LetParRegionE r sz _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv True r sz
          onDi (mkLets (region_lets)) <$> go freeVarToVarEnv' tenv senv bod

        FromEndE{} -> error $ "cursorizePackedExp: TODO " ++ sdoc ext

        BoundsCheck i bound cur -> return <$> dl <$> Ext $ L3.BoundsCheck i (((unwrapLocVar . toLocVar)) bound) (((unwrapLocVar . toLocVar)) cur)

        IndirectionE tycon dcon (from,from_reg) (to,to_reg) _ -> do
          dflags <- getDynFlags
          if gopt Opt_DisableGC dflags
             -- || (from_reg == "dummy" || to_reg == "dummy") -- HACK!!!
             -- [2022.03.02]: ckoparkar:WTH does this hack enable?
          then go freeVarToVarEnv tenv senv (DataConE from dcon [VarE (((unwrapLocVar . toLocVar)) to)])
          else do
            start <- gensym "start"
            end <- gensym "end"
            return $ Di $
              (mkLets [("_",[],ProdTy [],Ext (IndirectionBarrier tycon (((unwrapLocVar . toLocVar) from),((unwrapLocVar . toLocVar) from_reg),((unwrapLocVar . toLocVar) to),((unwrapLocVar . toLocVar) to_reg)))),
                       (start, [], CursorTy, VarE ((unwrapLocVar . toLocVar) from)),
                       (end, [], CursorTy, Ext $ AddCursor ((unwrapLocVar . toLocVar) from) (L3.LitE 9))]
                 (MkProdE [VarE start, VarE end]))

        AddFixed{} -> error "cursorizePackedExp: AddFixed not handled."

        GetCilkWorkerNum -> pure $ Di (Ext L3.GetCilkWorkerNum)

        LetAvail vs bod  -> do
          onDi (Ext . L3.LetAvail vs) <$> go freeVarToVarEnv tenv senv bod

        AllocateTagHere v tycon -> pure <$> dl <$> Ext $ L3.AllocateTagHere (unwrapLocVar v) tycon

        AllocateScalarsHere v -> pure <$> dl <$> Ext $ L3.AllocateScalarsHere (unwrapLocVar v)

        SSPush a b c d -> pure <$> dl <$> Ext $ L3.SSPush a (unwrapLocVar b) (unwrapLocVar c) d
        SSPop a b c -> pure <$> dl <$> Ext $ L3.SSPop a (unwrapLocVar b) (unwrapLocVar c)

    MapE{}  -> error $ "TODO: cursorizePackedExp MapE"
    FoldE{} -> error $ "TODO: cursorizePackedExp FoldE"

  where go env = cursorizePackedExp env lenv ddfs fundefs denv
        dl = Di


cursorizeReadPackedFile :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Bool -> Var
                        -> Maybe FilePath -> TyCon -> Maybe Var -> Ty2 -> Exp2
                        -> PassM Exp3
cursorizeReadPackedFile freeVarToVarEnv lenv ddfs fundefs denv tenv senv isPackedContext v path tyc reg ty2 bod = do
  case reg of
    Nothing -> error $ "cursorizePackedExp: InferLocations did not set the reg for ReadPackedFile."
    Just reg_var ->
      mkLets [ (v, [], CursorTy, PrimAppE (toL3Prim $ ReadPackedFile path tyc reg ty2) [])
             , (reg_var, [], CursorTy, VarE v)
             , (toEndV reg_var, [], CursorTy, Ext$ AddCursor reg_var (Ext $ MMapFileSize v))] <$>
         go (M.insert v (MkTy2 CursorTy) tenv) bod

  where
    go t e = if isPackedContext
             then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv t senv e
             else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv t senv e

-- We may sometimes encounter a letloc which uses an unbound location.
--
--     letloc loc_b = loc_a + 1
--
-- i.e `loc_a` may not always be bound. If that's the case, don't process `loc_b`
-- now. Instead, add it to the dependency environment.
cursorizeLocExp :: M.Map FreeVarsTy Var -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> LocVar -> LocExp -> Either DepEnv (Exp3, [Binds Exp3], TyEnv Var Ty2, SyncEnv)
cursorizeLocExp freeVarToVarEnv denv tenv senv lvar locExp =
  case locExp of
    AfterConstantLE i loc ->
      let locs_var = case (M.lookup ((fromLocVarToFreeVarsTy . toLocVar) loc) freeVarToVarEnv) of 
                        Just v -> v 
                        Nothing -> error $ "cursorizeLocExp: AfterConstantLE: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (toLocVar loc)) ++ ")" ++ show freeVarToVarEnv
          rhs = Ext $ AddCursor locs_var (LitE i)
          lvar_to_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                            Just v -> v 
                            Nothing -> error $ "cursorizeLocExp: AfterConstantLE: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show lvar) ++ ")" ++ show freeVarToVarEnv 
       in if isBound locs_var tenv
          then Right (rhs, [], tenv, senv)
          else Left$ M.insertWith (++) ((fromLocVarToFreeVarsTy . toLocVar) loc) [(lvar_to_name,[],CursorTy,rhs)] denv
    -- TODO: handle product types here

{- [2018.03.07]:

Changing it's meaning to just be "after a variable", but not offset from any
particular location. Such an offset requires calculating the size of the variable.
For BigInfinite regions, this is simple:

    size = (endof v) - v

But Infinite regions do not support sizes yet. Re-enable this later.
-}
    AfterVariableLE v locarg was_stolen -> do
      let vty = case M.lookup v tenv of
                  Just ty -> ty
                  Nothing -> case M.lookup v senv of
                               Just pending_bnds ->
                                 let tenv' = foldr (\(v1,_,_,ty2,_) env -> M.insert v1 ty2 env) tenv pending_bnds
                                 in case M.lookup v tenv' of
                                      Nothing -> error ("cursorizeLocExp: AfterVariableLE, undound var: " ++ sdoc v)
                                      Just ty -> ty
                               Nothing -> error $ "cursorizeLocExp: Var " ++ sdoc v ++ " not found. "
          loc = toLocVar locarg
          locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of 
                        Just v -> v 
                        Nothing -> error "cursorizeLocExp: AfterConstantLE: unexpected location variable" 
          bod = case unTy2 vty of
                  PackedTy{} -> VarE (toEndV v)
                  CursorTy   -> VarE (toEndV v)
{-
                  IntTy -> let sizeVal = LitE (fromJust $ sizeOfTy IntTy)
                               rhs = Ext $ AddCursor loc sizeVal
                           in rhs
                  FloatTy -> let sizeVal = LitE (fromJust $ sizeOfTy FloatTy)
                                 rhs = Ext $ AddCursor loc sizeVal
                             in rhs
                  BoolTy -> let sizeVal = LitE (fromJust $ sizeOfTy BoolTy)
                                rhs = Ext $ AddCursor loc sizeVal
                            in rhs
                  CharTy -> let sizeVal = LitE (fromJust $ sizeOfTy CharTy)
                                rhs = Ext $ AddCursor loc sizeVal
                            in rhs
                  SymTy -> let sizeVal = LitE (fromJust $ sizeOfTy SymTy)
                               rhs = Ext $ AddCursor loc sizeVal
                           in rhs
                  VectorTy elty -> let sizeVal = LitE (fromJust $ sizeOfTy (VectorTy elty))
                                       rhs = Ext $ AddCursor loc sizeVal
                                   in rhs
                  ListTy elty -> let sizeVal = LitE (fromJust $ sizeOfTy (ListTy elty))
                                     rhs = Ext $ AddCursor loc sizeVal
                                 in rhs
-}
                  oth -> error $ "cursorizeLocExp: AfterVariable TODO " ++ sdoc oth
          lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                              Just v -> v 
                              Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
      if isBound locs_var tenv
      then if was_stolen
           then Right (bod, [], tenv, senv)
           -- The continuation was not stolen. It's safe to discharge all
           -- pending bindings of this particular variable.
           else do
              case M.lookup v senv of
                Nothing -> Right (bod, [], tenv, senv)
                Just pending_bnds -> do
                  let tenv' = foldr (\(v1,_,_,ty2,_) env -> M.insert v1 ty2 env) tenv pending_bnds
                      bnds  = map (\(a,b,c,_,e) -> (a,b,c,e)) pending_bnds
                  Right (bod, bnds, tenv', M.delete v senv)
      else Left $ M.insertWith (++) (fromLocVarToFreeVarsTy loc) [(lvar_name,[],CursorTy,bod)] denv

    FromEndLE locarg ->
                   let loc = toLocVar locarg
                       locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of 
                              Just v -> v 
                              Nothing -> error $ "cursorizeLocExp: FromEndLE: unexpected location variable"  ++ "(" ++ show locExp ++ ", Location: " ++ (show (loc)) ++ ")" ++ show freeVarToVarEnv  
                       lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                              Just v -> v 
                              Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
                    in if isBound locs_var tenv
                     then Right (VarE locs_var, [], tenv, senv)
                     else Left$ M.insertWith (++) (fromLocVarToFreeVarsTy loc) [(lvar_name,[],CursorTy,VarE locs_var)] denv
    StartOfRegionLE r   -> case r of
                       GlobR v _ -> Right (VarE v, [], tenv, senv)
                       VarR v    -> Right (VarE v, [], tenv, senv)
                       DynR v _  -> Right (VarE v, [], tenv, senv)
                       -- TODO: docs
                       MMapR _v   -> Left denv
                       {- VS: TODO: This needs to be fixed. There should be an env. for tracking complex regions liks SoA regs-}
                       SoAR dr fregs ->
                          let regions_var = case (M.lookup (fromRegVarToFreeVarsTy (regionToVar r)) freeVarToVarEnv) of 
                                                Just v -> v 
                                                Nothing -> error "cursorizeLocExp: StartOfRegionLE: unexpected location variable" 
                        
                           in Right (VarE (regions_var), [], tenv, senv)


    FreeLE -> Left denv -- AUDIT: should we just throw away this information?

    InRegionLE{}  -> error $ "cursorizeExp: TODO InRegionLE"
    GetDataConLocSoA loc -> 
      {- VS: TODO: instead of using unwrap loc var, we should keep an env mapping a SoA loc to a L3 variable -}
      let loc_from_logarg = toLocVar loc
          loc_var = case (M.lookup (fromLocVarToFreeVarsTy loc_from_logarg) freeVarToVarEnv) of 
                        Just v -> v 
                        Nothing -> error "cursorizeLocExp: GetDataConLocSoA: unexpected location variable" 
          lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                        Just v -> v 
                        Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
          rhs = Ext $ IndexCursorArray loc_var 0
       in if isBound loc_var tenv
          then Right (rhs, [], tenv, senv)
          -- CursorArrayTy (1 + length (getAllFieldLocsSoA loc_from_logarg))
          else Left$ M.insertWith (++) (fromLocVarToFreeVarsTy loc_from_logarg) [(lvar_name,[],CursorTy,rhs)] denv
    GetFieldLocSoA i loc -> 
      {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
      let loc_from_locarg = toLocVar loc
          field_locs = getAllFieldLocsSoA loc_from_locarg 
          loc_var = case (M.lookup (fromLocVarToFreeVarsTy loc_from_locarg) freeVarToVarEnv) of 
                        Just v -> v 
                        Nothing -> error "cursorizeLocExp: GetDataConLocSoA: unexpected location variable"
          field_loc = case L.lookup i field_locs of 
                        Just loc -> loc
                        Nothing -> error "cursorizeLocExp: GetFieldLocSoA: field location not found!"
          field_loc_elem = (i, field_loc)
          elem_idx = case (L.elemIndex field_loc_elem field_locs) of 
                        Just idx -> idx
                        Nothing -> error "cursorizeLocExp: GetFieldLocSoA: field location not found!"
          lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                        Just v -> v 
                        Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
          rhs = Ext $ IndexCursorArray loc_var (1 + elem_idx) {- VS : We add one since the data constructor is reserved as the first element in the cursor Array -}
       in if isBound loc_var tenv
          then Right (rhs, [], tenv, senv)
          else Left$ M.insertWith (++) (fromLocVarToFreeVarsTy loc_from_locarg) [(lvar_name,[],CursorTy,rhs)] denv
    GenSoALoc dloc flocs ->
        {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}   
        let dcloc_var = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar dloc)) freeVarToVarEnv) of
                              Just v -> v 
                              Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected data constructor location variable" 
            field_vars = map (\(_, loc) -> case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of
                                                Just v -> v 
                                                Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable"
                             ) flocs
            rhs = Ext $ MakeCursorArray (1 + length flocs) ([dcloc_var] ++ field_vars)
         in dbgTrace (minChatLvl) "Print freeVarEnv GenSoALoc:" dbgTrace (minChatLvl) (sdoc (freeVarToVarEnv)) dbgTrace (minChatLvl) "End freeVarEnv\n"  Right (rhs, [], tenv, senv)
    
    _ -> error $ "cursorizeLocExp: Unexpected locExp: " ++ sdoc locExp

cursorizeRegExp :: M.Map FreeVarsTy Var -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> RegVar -> RegExp -> Either DepEnv (Exp3, [Binds Exp3], TyEnv Var Ty2, SyncEnv)
cursorizeRegExp freeVarToVarEnv denv tenv senv lvar regExp = 
  case regExp of 
        GetDataConRegSoA loc ->
          let loc_from_logarg = toLocVar loc
              reg_from_loc = fromLocVarToRegVar loc_from_logarg
              reg_var = case (M.lookup (fromRegVarToFreeVarsTy reg_from_loc) freeVarToVarEnv) of 
                                Just v -> v 
                                Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show regExp ++ "," ++ (show (reg_from_loc)) ++ ")" ++ show freeVarToVarEnv 
              rhs = Ext $ IndexCursorArray reg_var 0
              lvar_name = case (M.lookup (fromRegVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                                Just v -> v 
                                Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show regExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
            in if isBound reg_var tenv
            then Right (rhs, [], tenv, senv)
            -- CursorArrayTy (1 + length (getAllFieldLocsSoA loc_from_logarg))
            else Left$ M.insertWith (++) (fromRegVarToFreeVarsTy reg_from_loc) [(lvar_name,[],CursorTy,rhs)] denv
        GetFieldRegSoA i loc ->
          {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
          let loc_from_locarg = toLocVar loc
              field_locs = getAllFieldLocsSoA loc_from_locarg 
              reg_from_loc = fromLocVarToRegVar loc_from_locarg
              loc_var = case (M.lookup (fromRegVarToFreeVarsTy reg_from_loc) freeVarToVarEnv) of 
                            Just v -> v 
                            Nothing -> error "cursorizeRegExp: GetFieldRegSoA: unexpected location variable"
              field_loc = case L.lookup i field_locs of 
                            Just loc -> loc
                            Nothing -> error "cursorizeRegExp: GetFieldLocSoA: field location not found!"
              field_loc_elem = (i, field_loc)
              elem_idx = case (L.elemIndex field_loc_elem field_locs) of 
                            Just idx -> idx
                            Nothing -> error "cursorizeRegExp: GetFieldLocSoA: field location not found!"
              lvar_name = case (M.lookup (fromRegVarToFreeVarsTy lvar) freeVarToVarEnv) of 
                                Just v -> v 
                                Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show regExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
              rhs = Ext $ IndexCursorArray loc_var (1 + elem_idx) {- VS : We add one since the data constructor is reserved as the first element in the cursor Array -}
            in if isBound loc_var tenv
            then Right (rhs, [], tenv, senv)
            else Left$ M.insertWith (++) (fromRegVarToFreeVarsTy reg_from_loc) [(lvar_name,[],CursorTy,rhs)] denv



findSoAParent :: FreeVarsTy -> M.Map FreeVarsTy Var -> Maybe FreeVarsTy
findSoAParent fvar freeVarEnv = case fvar of
                                       R r -> let allKeys = M.keys freeVarEnv
                                                  parent = foldr (\k acc -> case k of 
                                                                            R r' -> case (findRegInRegion r' r) of 
                                                                                             Just regg -> Just regg 
                                                                                             Nothing -> acc
                                                                            FL l -> acc
                                                                            V v -> acc 
                                                                 ) Nothing allKeys
                                                in case parent of 
                                                       Just p -> Just $ R p
                                                       Nothing -> Nothing
                                       FL l -> Nothing
                                       V v -> Nothing

-- findSoAParentHelper :: FreeVarsTy -> FreeVarsTy -> Maybe FreeVarsTy
-- findSoAParentHelper a b = case (a, b) of
--                                 (R r1, R r2) -> if r1 == r2 
--                                                 then Just a 
--                                                 else case r1 of 
--                                                       SingleR _ -> Nothing 
--                                                       SoAR dcReg fieldRegs -> let check_fields = map (\r -> if r == r2 then Just r else Nothing) fieldRegs
--                                                                                 in   
--                                 FL l ->
--                                 V v ->  


findRegInRegion :: RegVar -> RegVar -> Maybe RegVar 
findRegInRegion r1 r2 = if r1 == r2 
                        then Just r1
                        else case r1 of
                              SingleR _ -> Nothing
                              SoARv dcReg fieldRegs -> case r2 of 
                                                            SingleR _ -> if dcReg == r2 then Just r1 else Nothing
                                                            SoARv _ _ -> let found = foldr (\(_ , fr) acc -> if fr == r2 then Just r1 else acc) Nothing fieldRegs
                                                                          in found



-- ASSUMPTIONS:
-- (1) `locs` has [in_regions, out_regions, in_locs, out_locs] for the function.
--     But after Cursorize, the calling convention changes so that input
--     locations appear last. Plus, `arg` would supply those. So we can
--     safely drop them from `locs`.
--
-- (2) We update `arg` so that all packed values in it only have start cursors.
cursorizeAppE :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeAppE freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex =
  case ex of
    AppE f locs args -> do
      let fnTy   = case M.lookup f fundefs of
                     Just g -> funTy g
                     Nothing -> error $ "Unknown function: " ++ sdoc f
          in_tys  = arrIns fnTy
          inLocs  = inLocVars fnTy
          numRegs = length (outRegVars fnTy) + length (inRegVars fnTy)
          -- Drop input locations, but keep everything else
          outs    = (L.take numRegs locs) ++  (L.drop numRegs $ L.drop (length inLocs) $ locs)
          argTys  = dbgTrace (minChatLvl) "Print locs in cursorize AppE " dbgTrace (minChatLvl) (sdoc (f, locs)) dbgTrace (minChatLvl) "End cursorize AppE\n" map (gRecoverType ddfs (Env2 tenv M.empty)) args
      (freeVarToVarEnv', newInsts) <- foldrM (\loc (acc, acc') -> do 
                                             let loc_var = fromLocArgToFreeVarsTy loc
                                             nacc <- case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                          Just v -> return (acc, acc')
                                                                          Nothing -> case loc_var of 
                                                                                            R r -> case r of 
                                                                                                              SingleR v -> return $ (M.insert loc_var v acc, acc')
                                                                                                              SoARv dconReg fieldRegions -> do
                                                                                                                -- let us try to find if the SoA region belongs to any other SoA region in the environment.
                                                                                                                            let parentRegion = findSoAParent loc_var acc
                                                                                                                            ret <- case parentRegion of 
                                                                                                                                      Just par_reg -> do 
                                                                                                                                                       let name_par_reg = case (M.lookup par_reg acc) of 
                                                                                                                                                                      Just v -> v 
                                                                                                                                                                      Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding parent region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc  
                                                                                                                                                       name <- gensym "cursor_reg_ptr"
                                                                                                                                                       let instrs = [LetE (name, [], CursorArrayTy (1 + length fieldRegions), Ext $ IndexCursorArray (name_par_reg) 1)]
                                                                                                                                                       return $ (M.insert loc_var name acc, acc' ++ instrs)
                                                                                                                                      Nothing -> do 
                                                                                                                                                  (dconReg_var, dcon_insts) <- case (M.lookup (fromRegVarToFreeVarsTy dconReg) acc) of 
                                                                                                                                                                                    Just v -> return (v, []) 
                                                                                                                                                                                    Nothing -> do
                                                                                                                                                                                                let parent_dcon_end = findSoAParent (fromRegVarToFreeVarsTy dconReg) acc
                                                                                                                                                                                                name_dcon <- case dconReg of 
                                                                                                                                                                                                                    SingleR s -> return s 
                                                                                                                                                                                                                    SoARv _ _ -> do 
                                                                                                                                                                                                                                 dnew_name <- gensym "dcon_end"
                                                                                                                                                                                                                                 return dnew_name 
                                                                                                                                                                                                case parent_dcon_end of 
                                                                                                                                                                                                        Just p -> do
                                                                                                                                                                                                                    let p_var_name = case (M.lookup p acc) of 
                                                                                                                                                                                                                                    Just v -> v 
                                                                                                                                                                                                                                    Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding parent region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc  
                                                                                                                                                                                                                    let instrs = [LetE (name_dcon, [], CursorTy, Ext $ IndexCursorArray (p_var_name) 0)]
                                                                                                                                                                                                                    return (name_dcon, instrs)

                                                                                                                                                                         -- Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding datacon region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc
                                                                                                                                                  let fieldReg_vars = map (\(key, field_reg) -> case (M.lookup (fromRegVarToFreeVarsTy field_reg) acc) of 
                                                                                                                                                       Just v -> v
                                                                                                                                                       Nothing -> error "cursorizeAppE: Did not find an end of region variable for the corresponding  field region.\n"
                                                                                                                                                                         ) fieldRegions
                                                                                                                                                  name <- gensym "cursor_reg_ptr"
                                                                                                                                                  let instrs = dcon_insts ++ [LetE (name, [], CursorArrayTy (1 + length fieldReg_vars), Ext $ MakeCursorArray (1 + length fieldReg_vars) ([dconReg_var] ++ fieldReg_vars))]
                                                                                                                                                  dbgTrace (minChatLvl) "Print Reg: " dbgTrace (minChatLvl) (sdoc (f, dconReg, fieldRegions)) dbgTrace (minChatLvl) "End soa Reg\n" return $ (M.insert loc_var name acc, acc' ++ instrs)
                                                                                                                            pure ret
                                                                                                                


                                                                                                                            -- may need to generate instructions to fetch correct end of regions here.
                                                                                                                            -- Right now I am just leaving this to one level of nesting, in the future this may need to be recursive.
                                                                                                                            -- let dconReg_var = case (M.lookup (fromRegVarToFreeVarsTy dconReg) acc) of 
                                                                                                                            --                         Just v -> v 
                                                                                                                            --                         Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding datacon region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc
                                                                                                                            -- let fieldReg_vars = map (\(key, field_reg) -> case (M.lookup (fromRegVarToFreeVarsTy field_reg) acc) of 
                                                                                                                            --                                                                         Just v -> v
                                                                                                                            --                                                                         Nothing -> error "cursorizeAppE: Did not find an end of region variable for the corresponding  field region.\n"
                                                                                                                            --                         ) fieldRegions
                                                                                                                            --name <- gensym "cursor_reg_ptr"
                                                                                                                            --let instrs = [LetE (name, [], CursorArrayTy (1 + length fieldReg_vars), Ext $ MakeCursorArray (1 + length fieldReg_vars) ([dconReg_var] ++ fieldReg_vars))]
                                                                                                                            --dbgTrace (minChatLvl) "Print Reg: " dbgTrace (minChatLvl) (sdoc (f, dconReg, fieldRegions)) dbgTrace (minChatLvl) "End soa Reg\n" return $ (M.insert loc_var name acc, acc' ++ instrs)
                                                                                            FL l -> case l of 
                                                                                                              Single v -> return $ (M.insert loc_var v acc, acc')
                                                                                                              SoA _ _ -> do
                                                                                                                            name <- gensym "cursor_ptr"
                                                                                                                            return $ (M.insert loc_var name acc, acc')
                                                                                            V v -> return $ (M.insert loc_var v acc, acc')
                                             return nacc
                                ) (freeVarToVarEnv, []) locs
      args' <- mapM
                 (\(t,a) -> if hasPacked (unTy2 t)
                            then fromDi <$> cursorizePackedExp freeVarToVarEnv' lenv ddfs fundefs denv tenv senv a
                            else cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv tenv senv a)
                 (zip in_tys args)
      let starts = zipWith giveStarts (map unTy2 argTys) args'
      --let loc_var = toLocVar loc
      --let loc_to_variable = case (M.lookup (fromLocVarToFreeVarsTy loc_var) freeVarToVarEnv) of 
      --                          Just v -> v 
      --                          Nothing -> error "cursorizeAppE: unexpected location variable"
      let bod = case locs of
                  [] -> AppE f [] starts
                  _  -> AppE f [] (map (\loc -> let loc_var = fromLocArgToFreeVarsTy loc
                                                    loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of 
                                                                          Just v -> v 
                                                                          Nothing -> error $ "cursorizeAppE: no variable for location" ++ show loc_var  
                                                  in VarE (loc_to_variable)
                                       ) outs ++ starts)
      asserts <- foldrM (\loc acc ->
                           case loc of
                             Loc LREM{lremEndReg,lremLoc} -> do
                               let lremEndRegToVar = case (M.lookup (fromRegVarToFreeVarsTy lremEndReg) freeVarToVarEnv') of 
                                                                 Just v -> v 
                                                                 Nothing -> error "cursorizeAppE: unexpected location variable"
                               let lremLocToVar = case (M.lookup (fromLocVarToFreeVarsTy lremLoc) freeVarToVarEnv') of 
                                                                 Just v -> v 
                                                                 Nothing -> error "cursorizeAppE: unexpected location variable"
                               chk <- gensym "chk"
                               pure $
                                 LetE (chk,[],BoolTy,PrimAppE LtP [VarE (lremLocToVar), VarE lremEndRegToVar]) $
                                 LetE ("_",[],ProdTy [], Ext $ Assert (VarE chk)) $
                                 acc
                             _ -> pure acc)
                        bod locs
      dflags <- getDynFlags
      if gopt Opt_RtsDebug dflags
        then do
          asserts' <- foldrM (\exprs body -> pure $ exprs body) asserts newInsts
          pure asserts'
        else do 
          bod' <- foldrM (\exprs body -> pure $ exprs body) bod newInsts 
          pure bod'
    _ -> error $ "cursorizeAppE: Unexpected " ++ sdoc ex

{-

Cursorizing projections
~~~~~~~~~~~~~~~~~~~~~~~

There are two ways in which projections can be cursorized:

    let pakd_tup = projE n something in
    let x        = projE 0 pakd_tup in
    let end_x    = projE 1 pakd_tup

    OR

    let x     = projE 0 (projE n something) in
    let end_x = projE 1 (projE n something)

`cursorizeLet` creates the former, while the special case here outputs the latter.
Reason: unariser can only eliminate direct projections of this form.
-}
cursorizeProj :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeProj freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex =
  case ex of
    LetE (v,_locs,ty, rhs@ProjE{}) bod | isPackedTy (unTy2 ty) -> do
      rhs' <- go tenv rhs
      let ty'  = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty'' = cursorizeTy (unTy2 ty')
          bnds = if isPackedTy (unTy2 ty')
                 then [ (v       ,[], projValTy ty'' , mkProj 0 rhs')
                      , (toEndV v,[], projEndsTy ty'', mkProj 1 rhs') ]
                 else [(v,[], ty'', rhs')]
          tenv' = if isPackedTy (unTy2 ty')
                  then M.union (M.fromList [(v,ty'), (toEndV v, MkTy2 (projEndsTy (unTy2 ty')))]) tenv
                  else M.insert v ty' tenv
      bod' <- go tenv' bod
      return $ mkLets bnds bod'

    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex

  where
    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv t senv x
             else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv t senv x


{-

Products and projections
~~~~~~~~~~~~~~~~~~~~~~~~

As per the dilated representation, all packed values are (start,end) tuples.
Except fn arguments and pattern matched vars (which are just start cursors).
So instead of using the type from the AST, which will always be `Packed`,
we recover type of RHS in the current type environment using gRecoverType.
If it's just `CursorTy`, this packed value doesn't have an end cursor,
otherwise, the type is `PackedTy{}`, and it also has an end cursor.

-}
cursorizeProd :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeProd freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex =
  case ex of
    LetE (v, _locs, MkTy2 (ProdTy tys), rhs@(MkProdE ls)) bod -> do
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
                  _ | hasPacked ty  -> fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
                  _ -> cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
      let rhs' = MkProdE es
          ty   = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty'  = cursorizeTy (unTy2 ty)
          tenv' = M.insert v ty tenv
      bod' <- go tenv' bod
      return $ mkLets [(v,[], ty', rhs')] bod'

    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex

  where
    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv t senv x
             else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv t senv x


{-

Spawn and sync
~~~~~~~~~~~~~~

This is almost identical to a cursorizeLet case below. Except we bind fewer things
and add fewer things to the type environemnt because we have to wait until the
join point.

-}
cursorizeSpawn :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeSpawn freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex = do
  case ex of
    LetE (v, locs, MkTy2 ty, (SpawnE fn applocs args)) bod

      | isPackedTy ty -> do
          rhs' <- fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv (AppE fn applocs args)
          let rhs'' = case rhs' of
                        AppE fn' applocs' args' -> SpawnE fn' applocs' args'
                        _ -> error "cursorizeSpawn"
          fresh <- gensym "tup_packed"
          let ty' = case locs of
                      [] -> cursorizeTy ty
                      xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])
              tenv' = M.union (M.fromList [(fresh, MkTy2 ty')]) tenv
                      -- L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                      --   [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]
              -- TyEnv Ty2 and L3 expresssions are tagged with different types
              ty''  = curDict $ stripTyLocs ty'
              fresh_rhs = VarE fresh
              (bnds, pending_bnds) =
                      case locs of
                        []    -> ([ (fresh   , [], ty''          , rhs'' ) ],
                                  [ (v       , [], projTy 0 ty'', MkTy2 ty            , mkProj 0 fresh_rhs)
                                  , (toEndV v, [], projTy 1 ty'', MkTy2 (projTy 1 ty'), mkProj 1 fresh_rhs)])
                        _ -> let nLocs = length locs
                                 locBnds = [((unwrapLocVar . toLocVar) loc  ,[], CursorTy, MkTy2 CursorTy, mkProj n fresh_rhs)
                                           | (loc,n) <- zip locs [0..]]
                                 bnds' = [(fresh ,[], ty'', rhs'') ]
                                 pending_bnds' = [(v       ,[], projTy 0 $ projTy nLocs ty'', MkTy2 ty,                            mkProj 0 $ mkProj nLocs fresh_rhs)
                                                 ,(toEndV v,[], projTy 1 $ projTy nLocs ty'', MkTy2 (projTy 0 $ projTy nLocs ty'), mkProj 1 $ mkProj nLocs fresh_rhs)]
                                                 ++ locBnds
                             in (bnds', pending_bnds')
          case M.lookup (fromVarToFreeVarsTy (toEndV v)) denv of
            Just xs -> error $ "cursorizeSpawn todo: " ++ sdoc xs
            Nothing -> return ()
          let senv' = M.insert v pending_bnds senv
          bod'  <- go tenv' senv' bod
          let bod'' = updateAvailVars [v] [fresh] bod'
          return $ mkLets bnds bod''

      | hasPacked ty -> do
          rhs' <- fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv (AppE fn applocs args)
          let rhs'' = case rhs' of
                        AppE fn' applocs' args' -> SpawnE fn' applocs' args'
                        _ -> error $ "cursorizeSpawn: this should've been an AppE. Got" ++ sdoc rhs'
          fresh <- gensym "tup_haspacked"
          let ty' = case locs of
                      [] -> cursorizeTy ty
                      xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])
              ty''  = stripTyLocs ty'
              tenv' = M.insert v (MkTy2 ty) tenv
          case locs of
            [] -> LetE (v,[], ty'', rhs'') <$>
                    go tenv' senv bod
            _  -> do
              let (bnds, pending_bnds) =
                    ([(fresh, [], ty'', rhs'')],
                     [((unwrapLocVar . toLocVar) loc,[],CursorTy, MkTy2 CursorTy, ProjE n (VarE fresh)) | (loc,n) <- (zip locs [0..])] ++
                     [(v           ,[], projTy (length locs) ty'', MkTy2 ty, ProjE (length locs) (VarE fresh))])
                  senv' = M.insert v pending_bnds senv
              mkLets bnds <$> go tenv' senv' bod

      | otherwise -> do
          rhs' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv (AppE fn applocs args)
          let rhs'' = case rhs' of
                        AppE fn' applocs' args' -> SpawnE fn' applocs' args'
                        _ -> error "cursorizeSpawn"
          case locs of
            [] -> LetE (v,[],curDict $ stripTyLocs ty, rhs'') <$>
                    go (M.insert v (MkTy2 ty) tenv) senv bod
            [loc] -> do
              fresh <- gensym "par_tup_scalar"
              let ty' :: OldTy2
                  ty'  = ProdTy ([CursorTy | _ <- locs] ++ [cursorizeTy ty])
                  tenv' = M.union (M.fromList [(fresh, MkTy2 ty')]) tenv
                  ty'' :: Ty3
                  ty'' = stripTyLocs ty'
                  rhs''' = Di (VarE fresh)
                  locs_name = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of 
                                Just v' -> v' 
                                Nothing -> error "cursorizeSpawn: unexpected location variable"
                  pending_bnds = [ (locs_name ,[] , projTy 0 ty'', MkTy2 (projTy 0 ty') , projVal rhs''')
                                 -- [2022.09.21]: Shouldn't this be projTy 1 ty'?
                                 , (v            ,[] , projTy 1 ty'', MkTy2 (projTy 1 ty') , projEnds rhs''')]
                  senv' = M.insert v pending_bnds senv
              bod' <- go tenv' senv' bod
              return $ mkLets [(fresh,[] , ty'', rhs'')] bod'

            _ -> error "TODO: cursorizeSpawn"

    _ -> error "cursorizeSpawn: Unbound SpawnE"

  where go t s x = if isPackedContext
                   then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv t s x
                   else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv t s x

cursorizeSync :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeSync freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex = do
  case ex of
    LetE (v, _locs, MkTy2 ty, SyncE) bod -> do
      let pending_bnds = concat (M.elems senv)
          tenv' = foldr (\(v1,_,_,ty2,_) env -> M.insert v1 ty2 env) tenv pending_bnds
          -- Discharge bindings that depending on the join point.
          bnds  = map (\(a,b,c,_,e) -> (a,b,c,e)) pending_bnds
          bnds' = (v,[],stripTyLocs ty, SyncE) : bnds
      bod' <- go tenv' bod
      return $ mkLets bnds' bod'
    _ -> error "cursorizeSpawn: Unbound SyncE"
  where go t x = if isPackedContext
                 then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv t M.empty x
                 else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv t M.empty x


{-

Cursorizing let expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Process RHS and bind the following cursors

     v     -> start_write
     end_v -> end_write
     loc   -> end_read     (only if it's available)

An expression returning packed value can either be a `DataConE` or a `AppE`.
DataConE returns a (start_write,end_write) tuple whereas
AppE returns (end_read,end_write).

So we cannot always rely on the RHS to return a start_write cursor.
But since the types of all packed expressions are already annotated with locations,
we can take a shortcut here and directly bind `v` to the tagged location.

Other bindings are straightforward projections of the processed RHS.

-}
cursorizeLet :: M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv
             -> (Var, [LocArg], Ty2, Exp2) -> Exp2 -> PassM Exp3
cursorizeLet freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv (v,locs,(MkTy2 ty),rhs) bod
    | isPackedTy ty = do
        rhs' <- fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rhs
        fresh <- dbgTrace (minChatLvl) "Print locs in cursorize Let " dbgTrace (minChatLvl) (sdoc (locs)) dbgTrace (minChatLvl) "End cursorize Let\n" gensym "tup_packed"
        let cursor_ty_locs = map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                              cursorType = case free_var of
                                                        R r -> case r of 
                                                                    SingleR _ -> CursorTy
                                                                    SoARv _ flds -> CursorArrayTy (1 + length flds)
                                                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                                                        FL l -> case l of 
                                                                    Single _ -> CursorTy
                                                                    SoA _ flds -> CursorArrayTy (1 + length flds)
                                            in cursorType
                                 ) locs
        let cursor_ty_locs' = map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                               cursorType :: Ty3 = case free_var of 
                                                        R r -> case r of 
                                                                    SingleR _ -> CursorTy
                                                                    SoARv _ flds -> CursorArrayTy (1 + length flds)
                                                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                                                        FL l -> case l of 
                                                                    Single _ -> CursorTy
                                                                    SoA _ flds -> CursorArrayTy (1 + length flds)
                                            in cursorType
                                 ) locs
        let ty' = case locs of
                    [] -> cursorizeTy ty
                    xs -> ProdTy ( cursor_ty_locs ++ [cursorizeTy ty])

            tenv' = L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                      [(v, MkTy2 ty),(fresh, MkTy2 ty'),(toEndV v, MkTy2 (projTy 1 ty'))] ++
                      map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                       var = case (M.lookup free_var freeVarToVarEnv) of 
                                                Just v -> v 
                                                Nothing -> error "cursorizeLet: unexpected location variable"
                                       cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)          
                                     in (var, MkTy2 cursorType)
                          ) locs

            -- TyEnv Ty2 and L3 expresssions are tagged with different types
            ty''  = curDict $ stripTyLocs ty'
            rhs'' = VarE fresh

            bnds = case locs of
                      []    -> [ (fresh   , [], ty''          , rhs' )
                               , (v       , [], projTy 0 ty'' , mkProj 0 rhs'')
                               , (toEndV v, [], projTy 1 ty'' , mkProj 1 rhs'')]

                      _ -> let nLocs = length locs
                               locBnds = map (\(loc, n) -> let loc_var = fromLocArgToFreeVarsTy loc
                                                               cursor_ty = cursor_ty_locs' !! n
                                                               loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                                      Just v -> v 
                                                                                      Nothing -> error "cursorizeLet: unexpected location variable"
                                                            in (loc_to_variable, [], cursor_ty, mkProj n rhs'')
                                             ) (zip locs [0..])
                               bnds' = [(fresh   ,[], ty''                         , rhs')
                                       ,(v       ,[], projTy 0 $ projTy nLocs ty'' , mkProj 0 $ mkProj nLocs rhs'')
                                       ,(toEndV v,[], projTy 1 $ projTy nLocs ty'' , mkProj 1 $ mkProj nLocs rhs'')]
                           in bnds' ++ locBnds
        case M.lookup (fromVarToFreeVarsTy (toEndV v)) denv of
          Just xs -> error $ "todo: " ++ sdoc xs
          Nothing -> return ()
        bod' <- go tenv' bod
        return $ mkLets bnds bod'

    | hasPacked ty = do
        let cursor_ty_locs = map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                              cursorType = case free_var of 
                                                        R r -> case r of 
                                                                    SingleR _ -> CursorTy
                                                                    SoARv _ flds -> CursorArrayTy (1 + length flds)
                                                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                                                        FL l -> case l of 
                                                                    Single _ -> CursorTy
                                                                    SoA _ flds -> CursorArrayTy (1 + length flds)
                                            in cursorType
                                 ) locs
        let cursor_ty_locs' = map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                               cursorType :: Ty3 = case free_var of 
                                                        R r -> case r of 
                                                                    SingleR _ -> CursorTy
                                                                    SoARv _ flds -> CursorArrayTy (1 + length flds)
                                                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                                                        FL l -> case l of 
                                                                    Single _ -> CursorTy
                                                                    SoA _ flds -> CursorArrayTy (1 + length flds)
                                            in cursorType
                                 ) locs
        rhs' <- fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rhs
        fresh <- gensym "tup_haspacked"
        let ty' = case locs of
                    [] -> cursorizeTy ty
                    xs -> ProdTy (cursor_ty_locs ++ [cursorizeTy ty])
            ty''  = stripTyLocs ty'
            tenv' = M.union (M.insert v (MkTy2 ty) tenv) (M.fromList $ map (\loc -> let loc_var = fromLocArgToFreeVarsTy loc 
                                                                                        loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                                                              Just v -> v 
                                                                                                              Nothing -> error "cursorizeLet: unexpected location variable"
                                                                                        cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                                                                                      in (loc_to_variable, MkTy2 cursorType)
                                                                            ) locs)
        case locs of
          [] -> LetE (v,[], ty'', rhs') <$>
                  go tenv' bod
          _  -> do
            let tenv'' =  M.union tenv' $
                          M.fromList $ map (\loc -> let loc_var = fromLocArgToFreeVarsTy loc 
                                                        loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                                            Just v' -> v' 
                                                                                            Nothing -> error "cursorizeLet: unexpected location variable"
                                                        cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                                                      in (loc_to_variable, MkTy2 cursorType)
                                           ) locs

                bnds  = [(fresh, [], ty'', rhs')] ++
                        map (\(loc, n) -> let loc_var = fromLocArgToFreeVarsTy loc
                                              loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                                      Just v' -> v' 
                                                                                      Nothing -> error "cursorizeLet: unexpected location variable"
                                              cursorType = cursor_ty_locs' !! n 
                                           in (loc_to_variable, [], cursorType, ProjE n (VarE fresh))
                        
                            ) (zip locs [0..])
                        ++ [(v,[], projTy (length locs) ty'', ProjE (length locs) (VarE fresh))]
            mkLets bnds <$> go tenv'' bod

  {-

This was a scalar binding before, but now has been transformed to
also return an end_read cursor. So the type of the binding now
becomes:

    ProdTy [CursorTy, old_ty]

Also, the binding itself now changes to:

    end_read -> ProjE 0 RHS'
    v        -> ProjE 1 RHS'

`rightmost` is an example of a program that does this.

-}

    | otherwise = do
        let cursor_ty_locs = map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                              cursorType = case free_var of 
                                                        R r -> case r of 
                                                                    SingleR _ -> CursorTy
                                                                    SoARv _ flds -> CursorArrayTy (1 + length flds)
                                                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                                                        FL l -> case l of 
                                                                    Single _ -> CursorTy
                                                                    SoA _ flds -> CursorArrayTy (1 + length flds)
                                            in cursorType
                                 ) locs
        let cursor_ty_locs' = map (\loc -> let free_var = fromLocArgToFreeVarsTy loc
                                               cursorType :: Ty3 = case free_var of 
                                                        R r -> case r of 
                                                                    SingleR _ -> CursorTy
                                                                    SoARv _ flds -> CursorArrayTy (1 + length flds)
                                                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                                                        FL l -> case l of 
                                                                    Single _ -> CursorTy
                                                                    SoA _ flds -> CursorArrayTy (1 + length flds)
                                            in cursorType
                                 ) locs
        rhs' <- cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv tenv senv rhs
        case locs of
            [] -> LetE (v,[],curDict $ stripTyLocs ty, rhs') <$>
                    go (M.insert v (MkTy2 ty) tenv) bod
            _ -> do
              fresh <- gensym "tup_scalar"
              let rhs'' = VarE fresh
                  ty'  = ProdTy (cursor_ty_locs ++ [cursorizeTy ty])
                  -- We cannot resuse ty' here because TyEnv Ty2 and expresssions are
                  -- tagged with different
                  ty'' = stripTyLocs ty'
                  tenv' =  M.union (M.insert v (MkTy2 ty) tenv) $
                           M.fromList $ map (\loc -> let loc_var = fromLocArgToFreeVarsTy loc
                                                         loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                                      Just v -> v 
                                                                                      Nothing -> error "cursorizeLet: unexpected location variable"
                                                         cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                                                      in (loc_to_variable, MkTy2 cursorType)) locs
                  bnds  = [ (fresh, [] , ty''          , rhs') ] ++
                          map (\(loc, n) -> let loc_var = fromLocArgToFreeVarsTy loc 
                                                loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv) of 
                                                                                      Just v -> v 
                                                                                      Nothing -> error "cursorizeLet: unexpected location variable"
                                                cursorType = cursor_ty_locs' !! n 
                                             in (loc_to_variable, [], cursorType, ProjE n rhs'')
                              ) (zip locs [0..]) ++
                          [ (v,[], projTy (length locs) ty'', ProjE (length locs) rhs'') ]
              bod' <- go tenv' bod
              return $ mkLets bnds bod'

  where go t x = if isPackedContext
                 then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv t senv x
                 else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv t senv x

{-

Unpacking constructors
~~~~~~~~~~~~~~~~~~~~~~

(1) Take a cursor pointing to the start of the tag, and advance it by 1 byte.
(2) If this DataCon has random access nodes, unpack those.
(3) If the first bound varaible is a scalar (IntTy), read it using the newly
returned cursor. Otherwise, just process the body. it'll have the correct
instructions to process other bound locations

Consider an example of unpacking of a Node^ pattern:

    (Node^ [(ind_y3, loc_ind_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)]
      BODY)

..TODO..

-}
unpackDataCon :: Var -> M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Bool -> Var
              -> (DataCon, [(Var, LocArg)], Exp2) -> PassM (DataCon, [t], Exp3)
unpackDataCon dcon_var freeVarToVarEnv lenv ddfs fundefs denv1 tenv1 senv isPacked scrtCur (dcon,vlocs1,rhs) = do
  field_cur <- gensym "field_cur"
  let ty_of_scrut = case (M.lookup scrtCur tenv1) of 
                            Just (MkTy2 ty) -> ty
                            Nothing -> error "unpackDataCon: unexpected location variable"

  case ty_of_scrut of 
    CursorTy -> (dcon, [],)
                -- Advance the cursor by 1 byte so that it points to the first field
                <$> mkLets [(field_cur,[],CursorTy, Ext $ AddCursor scrtCur (LitE 1))]
                <$> (if isAbsRANDataCon dcon
                     then unpackWithAbsRAN field_cur
                     else if isRelRANDataCon dcon
                     then unpackWithRelRAN field_cur
                     else unpackRegularDataCon (AoSWin field_cur) freeVarToVarEnv)
    CursorArrayTy size -> do
                          -- dcon_var <- gensym "dcon" 
                          let first_var = field_cur
                          let scrut_loc = case (M.lookup scrtCur lenv) of 
                                                                  Just loc -> case loc of
                                                                                  Just l -> case l of 
                                                                                                Single _ -> error "unpackDataCon: Did not expect a single location for a cursor array!"
                                                                                                SoA _ _ -> l
                                                                                  Nothing -> error "unpackDataCon: Did not find a location for scrutinee!"
                                                                  Nothing -> error "unpackDataCon: Did not find a location for scrutinee!"
                          
                          -- let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray scrtCur 0)]
                          (field_lets, field_v_lst, freeVarToVarEnv') <- dbgTrace (minChatLvl) "Print scrut_loc " dbgTrace (minChatLvl) (sdoc ((dcon, scrut_loc))) dbgTrace (minChatLvl) "end scrut_loc.\n" 
                                                        foldlM (\(acc1, acc2, acc3) (key@(dcon', idx), loc) -> do
                                                                        let idx_elem = fromJust $ L.elemIndex (key, loc) (getAllFieldLocsSoA scrut_loc)
                                                                        field_var <- gensym $ toVar $ (fromVar "soa_field_") ++ (show idx_elem)
                                                                        let acc3' = dbgTrace (minChatLvl) "print loc: " dbgTrace (minChatLvl) (sdoc (loc, scrut_loc)) dbgTrace (minChatLvl) "End cursorize print loc.\n" M.insert (fromLocVarToFreeVarsTy loc) field_var acc3
                                                                        let field_cursor_ty = case loc of 
                                                                                                    Single _ -> CursorTy
                                                                                                    SoA _ flds -> CursorArrayTy (1 + L.length (flds)) 
                                                                        let field_let = [(field_var, [], field_cursor_ty, Ext $ IndexCursorArray scrtCur (1+idx_elem))]
                                                                        let curr_window = [((dcon', idx), field_var)]
                                                                        return (acc1 ++ field_let , acc2 ++ curr_window, acc3')
                                                              ) ([], [], freeVarToVarEnv) (getAllFieldLocsSoA scrut_loc)
                          bod <- (if isAbsRANDataCon dcon
                                then unpackWithAbsRAN field_cur
                                else if isRelRANDataCon dcon
                                then unpackWithRelRAN field_cur
                                else unpackRegularDataCon (SoAWin dcon_var field_v_lst) freeVarToVarEnv')
                          let lets = mkLets (field_lets) bod
                          dbgTrace (minChatLvl) "Print scrut loc: " dbgTrace (minChatLvl) (sdoc scrut_loc) dbgTrace (minChatLvl) "End loc\n" return (dcon, [], lets)
    _ -> (dcon, [],)
                -- Advance the cursor by 1 byte so that it points to the first field
                <$> mkLets [(field_cur,[],CursorTy, Ext $ AddCursor scrtCur (LitE 1))]
                <$> (if isAbsRANDataCon dcon
                     then unpackWithAbsRAN field_cur
                     else if isRelRANDataCon dcon
                     then unpackWithRelRAN field_cur
                     else unpackRegularDataCon (AoSWin field_cur) freeVarToVarEnv)
    
  where
    tys1 = lookupDataCon ddfs dcon
    processRhs denv env = if isPacked
                          then fromDi <$> cursorizePackedExp freeVarToVarEnv lenv ddfs fundefs denv env senv rhs
                          else cursorizeExp freeVarToVarEnv lenv ddfs fundefs denv env senv rhs

    lookupVariable :: FreeVarsTy -> M.Map FreeVarsTy Var -> PassM Var
    lookupVariable loc fenv = case (M.lookup loc fenv) of 
                                  Just v -> return v
                                  Nothing -> error "lookupVariable: unexpected location variable"    

    -- Since this constructor does not have random access nodes, we may not be able
    -- to unpack all the fields. Basically, anything after the first packed
    -- value isn't accessible since we have no way to reach it without knowing
    -- the end of the packed value. So we punt on creating bindings for such
    -- variables, and add them to the dependency environment instead. Later, when
    -- the appropriate end locations become available (see the LetLocE cases),
    -- these bindings are discharged from the dependency environment.
    --
    -- We recurse over the fields in `go`, and create bindings as long as we `canBind`.
    -- Otherwise, we add things to the dependency environment. `canBind` is set
    -- to true initially, and we flip it as soon as we see a packed value.
    --
    unpackRegularDataCon :: WindowIntoCursor -> M.Map FreeVarsTy Var -> PassM Exp3
    unpackRegularDataCon field_cur freeVarToVarEnv_unpack = do 
      let tenv1' = case field_cur of 
                        AoSWin cf -> (M.insert cf (MkTy2 CursorTy) tenv1)
                        SoAWin dcf fieldfvs -> let tenv1'' = M.insert dcf (MkTy2 CursorTy) tenv1 
                                                 in foldr (\(x,y) acc -> M.insert y (MkTy2 CursorTy) acc) tenv1'' fieldfvs
      exp_unp <- go field_cur freeVarToVarEnv_unpack vlocs1 tys1 True denv1 tenv1'
      return exp_unp
      where
        go :: WindowIntoCursor -> M.Map FreeVarsTy Var -> [(Var, LocArg)] -> [Ty2] -> Bool -> DepEnv -> TyEnv Var Ty2 -> PassM Exp3
        go curw fenv vlocs tys canBind denv tenv = do 
          case curw of
            AoSWin cur -> do 
              case (vlocs, tys) of
                ([],[]) -> processRhs denv tenv
                ((v,locarg):rst_vlocs, (MkTy2 ty):rst_tys) ->
                  let loc = fromLocArgToFreeVarsTy locarg
                    in case ty of
                    -- Int, Float, Sym, or Bool
                    _ | isScalarTy ty -> do
                      loc_var <- lookupVariable loc fenv
                      (tenv', binds) <- scalarBinds ty v loc_var tenv
                      if canBind
                      then do
                        -- If the location exists in the environment, it indicates that the
                        -- corresponding variable was also bound and we shouldn't create duplicate
                        -- bindings (checked in the LetLocE cases).
                        loc_var <- lookupVariable loc fenv
                        let binds' = ((loc_var),[],CursorTy, VarE cur):binds
                            tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        bod <- go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv''
                        return $ mkLets binds' bod
                      else do
                        -- Cannot read this int. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) binds denv
                        go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv' tenv'

                    -- An indirection or redirection pointer.
                    -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                    CursorTy -> do
                      tmp <- gensym "readcursor_indir"
                      loc_var <- lookupVariable loc fenv
                      let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                      ((loc_var)     , MkTy2 CursorTy),
                                                       (v       , MkTy2 CursorTy),
                                                      (toEndV v, MkTy2 CursorTy),
                                                       (toTagV v, MkTy2 IntTy),
                                                       (toEndFromTaggedV v, MkTy2 CursorTy)])
                                  tenv
                          read_cursor = if isIndirectionTag dcon || isRedirectionTag dcon
                                        then Ext (ReadTaggedCursor cur)
                                        else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                          binds = [(tmp     , [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                   ((loc_var)     , [], CursorTy, VarE cur),
                                   (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                                   (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                   (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                   (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))]
                      bod <- go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv'
                      return $ mkLets binds bod


                    VectorTy el_ty -> do
                      tmp <- gensym "read_vec_tuple"
                      loc_var <- lookupVariable loc fenv
                      let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                                       (v       , MkTy2 (VectorTy el_ty)),
                                                       (toEndV v, MkTy2 CursorTy)])
                                 tenv
                          ty'   = stripTyLocs ty
                          binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadVector (loc_var) (stripTyLocs el_ty)),
                                   (v       , [], ty'     , ProjE 0 (VarE tmp)),
                                   (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      if canBind
                      then do
                        -- If the location exists in the environment, it indicates that the
                        -- corresponding variable was also bound and we shouldn't create duplicate
                        -- bindings (checked in the LetLocE cases).
                        loc_var <- lookupVariable loc fenv
                        let binds' = ((loc_var),[],CursorTy, VarE cur):binds
                            tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        bod <- go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv''
                        return $ mkLets binds' bod
                      else do
                        -- Cannot read this int. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) binds denv
                        go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv' tenv'


                    ListTy el_ty -> do
                      tmp <- gensym "read_list_tuple"
                      loc_var <- lookupVariable loc fenv
                      let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [ListTy el_ty, CursorTy])),
                                                       (v       , MkTy2 (ListTy el_ty)),
                                                       (toEndV v, MkTy2 CursorTy)])
                                 tenv
                          ty'   = stripTyLocs ty
                          binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadList (loc_var) (stripTyLocs el_ty)),
                                   (v       , [], ty'     , ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      if canBind
                      then do
                        -- If the location exists in the environment, it indicates that the
                        -- corresponding variable was also bound and we shouldn't create duplicate
                        -- bindings (checked in the LetLocE cases).
                        loc_var <- lookupVariable loc fenv
                        let binds' = ((loc_var),[],CursorTy, VarE cur):binds
                            tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        bod <- go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv''
                        return $ mkLets binds' bod
                      else do
                        -- Cannot read this int. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) binds denv
                        go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv' tenv'

                    PackedTy _ ploc -> do
                      let tenv' = M.insert v (MkTy2 CursorTy) tenv
                      loc_var <- lookupVariable loc fenv
                      if canBind
                      then do
                        let tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        -- Flip canBind to indicate that the subsequent fields
                        -- should be added to the dependency environment.
                        bod <- go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys False denv tenv''
                        return $ mkLets [((loc_var), [], CursorTy, VarE cur)
                                        ,(v  , [], CursorTy, VarE (loc_var))]
                                 bod
                      else do
                        -- Cannot read this. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) [(v,[],CursorTy,VarE (loc_var))] denv
                        go (AoSWin (toEndV v)) fenv rst_vlocs rst_tys False denv' tenv'

                    _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

                _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)
            {- VS: TODO: handle other cases. Right now, it is only scalar and packed -}
            SoAWin dcur field_cur -> do 
              case (vlocs, tys) of
                ([],[]) -> processRhs denv tenv
                ((v,locarg):rst_vlocs, (MkTy2 ty):rst_tys) ->
                  let loc = fromLocArgToFreeVarsTy locarg
                    in case ty of
                    -- Int, Float, Sym, or Bool
                    _ | isScalarTy ty -> do
                      loc_var <- lookupVariable loc fenv
                      (tenv', binds) <- scalarBinds ty v loc_var tenv
                      let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                      let field_cur' = map (\(k@(d, idx), var) -> if (d, idx) == (dcon, field_idx) then (k, (toEndV v)) else (k, var)) field_cur
                      let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                      if canBind
                      then do
                        -- If the location exists in the environment, it indicates that the
                        -- corresponding variable was also bound and we shouldn't create duplicate
                        -- bindings (checked in the LetLocE cases).
                        loc_var <- lookupVariable loc fenv
                        let binds' = ((loc_var),[],CursorTy, VarE cur):binds
                            tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        
                        bod <- go (SoAWin dcur field_cur') fenv rst_vlocs rst_tys canBind denv tenv''
                        return $ mkLets binds' bod
                      else do
                        -- Cannot read this int. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) binds denv
                        go (SoAWin dcur field_cur') fenv rst_vlocs rst_tys canBind denv' tenv'

                    -- An indirection or redirection pointer.
                    -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                    CursorTy -> do
                      tmp <- gensym "readcursor_indir"
                      loc_var <- lookupVariable loc fenv
                      let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                      let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                      let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                      ((loc_var)     , MkTy2 CursorTy),
                                                       (v       , MkTy2 CursorTy),
                                                      (toEndV v, MkTy2 CursorTy),
                                                       (toTagV v, MkTy2 IntTy),
                                                       (toEndFromTaggedV v, MkTy2 CursorTy)])
                                  tenv
                          read_cursor = if isIndirectionTag dcon || isRedirectionTag dcon
                                        then Ext (ReadTaggedCursor cur)
                                        else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                          binds = [(tmp     , [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                   ((loc_var)     , [], CursorTy, VarE cur),
                                   (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                                   (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                   (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                   (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))]
                      bod <- go curw fenv rst_vlocs rst_tys canBind denv tenv' -- (toEndV v)
                      return $ mkLets binds bod


                    VectorTy el_ty -> do
                      tmp <- gensym "read_vec_tuple"
                      loc_var <- lookupVariable loc fenv
                      let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                                       (v       , MkTy2 (VectorTy el_ty)),
                                                       (toEndV v, MkTy2 CursorTy)])
                                 tenv
                          ty'   = stripTyLocs ty
                          binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadVector (loc_var) (stripTyLocs el_ty)),
                                   (v       , [], ty'     , ProjE 0 (VarE tmp)),
                                   (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                      let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                      if canBind
                      then do
                        -- If the location exists in the environment, it indicates that the
                        -- corresponding variable was also bound and we shouldn't create duplicate
                        -- bindings (checked in the LetLocE cases).
                        loc_var <- lookupVariable loc fenv
                        let binds' = ((loc_var),[],CursorTy, VarE cur):binds
                            tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        bod <- go curw fenv rst_vlocs rst_tys canBind denv tenv'' --(toEndV v)
                        return $ mkLets binds' bod
                      else do
                        -- Cannot read this int. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) binds denv
                        go curw fenv rst_vlocs rst_tys canBind denv' tenv' --(toEndV v)


                    ListTy el_ty -> do
                      tmp <- gensym "read_list_tuple"
                      loc_var <- lookupVariable loc fenv
                      let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                      let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                      let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [ListTy el_ty, CursorTy])),
                                                       (v       , MkTy2 (ListTy el_ty)),
                                                       (toEndV v, MkTy2 CursorTy)])
                                 tenv
                          ty'   = stripTyLocs ty
                          binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadList (loc_var) (stripTyLocs el_ty)),
                                   (v       , [], ty'     , ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      if canBind
                      then do
                        -- If the location exists in the environment, it indicates that the
                        -- corresponding variable was also bound and we shouldn't create duplicate
                        -- bindings (checked in the LetLocE cases).
                        loc_var <- lookupVariable loc fenv
                        let binds' = ((loc_var),[],CursorTy, VarE cur):binds
                            tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                        bod <- go curw fenv rst_vlocs rst_tys canBind denv tenv'' --(toEndV v)
                        return $ mkLets binds' bod
                      else do
                        -- Cannot read this int. Instead, we add it to DepEnv.
                        let denv' = M.insertWith (++) (loc) binds denv
                        go curw fenv rst_vlocs rst_tys canBind denv' tenv' --(toEndV v)

                    PackedTy tycon ploc -> do
                      -- Two cases 
                      -- If the PackedTy is the same tycon then
                      -- If the PackedTy is not the same tycon
                      let datacons = getConOrdering ddfs tycon 
                      let isSameTycon = if (elem dcon datacons) then True else False
                      case isSameTycon of 
                        True -> do 
                          let ty3_of_field = case ploc of 
                                                  Single _ -> CursorTy
                                                  SoA _ fl -> CursorArrayTy (1 + length fl)
                          let ty3_of_field2 :: Ty3 = case ploc of 
                                                        Single _ -> CursorTy
                                                        SoA _ fl -> CursorArrayTy (1 + length fl)
                          let tenv' = M.insert v (MkTy2 ty3_of_field) tenv
                          let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                          -- let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                          let cur = dcur
                          loc_var <- lookupVariable loc fenv
                          if canBind
                          then do
                            let tenv'' = M.insert (loc_var) (MkTy2 ty3_of_field) tenv'
                            -- Flip canBind to indicate that the subsequent fields
                            -- should be added to the dependency environment.
                            dcon_next <- gensym $ toVar $ (fromVar dcur) ++ "_next"
                            let end_fields = map (\(key, varr) -> varr ) field_cur
                            let makeCurArr = Ext $ MakeCursorArray (1 + length (end_fields)) ([dcon_next] ++ end_fields)
                            let let_mk_cur_arr = (loc_var, [], CursorArrayTy (1 + length (end_fields)), makeCurArr)
                            let dcon_nxt = [(dcon_next,[],CursorTy, Ext $ AddCursor dcur (LitE 1))] ++ [let_mk_cur_arr,(v  , [], CursorArrayTy (1 + length (end_fields)), VarE (loc_var))]
                            -- make the new curw type 
                            -- this consists of incrementing the data constructor buffer by one and all the rest of the fields 
                            let curw' = SoAWin dcon_next field_cur
                            bod <- go curw' fenv rst_vlocs rst_tys False denv tenv'' --(toEndV v)
                            return $ mkLets dcon_nxt bod
                          else do
                            -- Cannot read this. Instead, we add it to DepEnv.
                            let denv' = M.insertWith (++) (loc) [(v,[],ty3_of_field2,VarE (loc_var))] denv
                            go curw  fenv rst_vlocs rst_tys False denv' tenv' --(toEndV v)
                        False -> do
                          let ty3_of_field = case ploc of 
                                                  Single _ -> CursorTy
                                                  SoA _ fl -> CursorArrayTy (1 + length fl)
                          let ty3_of_field2 :: Ty3 = case ploc of 
                                                        Single _ -> CursorTy
                                                        SoA _ fl -> CursorArrayTy (1 + length fl)
                          let tenv' = M.insert v (MkTy2 ty3_of_field) tenv
                          let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                          let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                          -- let cur = dcur
                          loc_var <- lookupVariable loc fenv
                          if canBind
                          then do
                            let tenv'' = M.insert (loc_var) (MkTy2 ty3_of_field) tenv'
                            -- Flip canBind to indicate that the subsequent fields
                            -- should be added to the dependency environment.
                            bod <- go curw fenv rst_vlocs rst_tys False denv tenv'' --(toEndV v)
                            return $ mkLets [((loc_var), [], ty3_of_field2, VarE cur)
                                        ,(v  , [], ty3_of_field2, VarE (loc_var))]
                                     bod
                          else do
                            -- Cannot read this. Instead, we add it to DepEnv.
                            let denv' = dbgTrace (minChatLvl) "Printing in packedTy unpack dcon: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End in unpacking dcon.\n" M.insertWith (++) (loc) [((loc_var), [], ty3_of_field2, VarE cur), (v,[],ty3_of_field2,VarE (loc_var))] denv
                            bod <- go curw  fenv rst_vlocs rst_tys False denv' tenv' --(toEndV v)
                            -- VS: [05.11.2025] This is a hack to ensure that the location variable is not undefined. 
                            -- If we have serialized packed types that are not self recursive, we still have to release 
                            -- The let binding and just adding it to the depenv is not enough. 
                            -- There should be a careful look at why this is and if this is functionally correct. 
                            return $ mkLets [((loc_var), [], ty3_of_field2, VarE cur), (v  , [], ty3_of_field2, VarE (loc_var))]
                                     bod
                    _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

                _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)


          
      

    -- We have access to all fields in this constructor, and can create
    -- bindings for everything. We begin by unpacking the random access nodes.
    unpackWithAbsRAN :: Var -> PassM Exp3
    unpackWithAbsRAN field_cur =
        -- A map from a variable to a tuple containing it's location and
        -- the RAN field it depends on. Consider this constructor:
        --
        --     (Node^ [(ran_y3, loc_ran_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)] ...),
        --
        -- it will be the map:
        --
        --     (y3 -> (loc_y3, ran_y3))
        let ran_mp =
              case numRANsDataCon (M.map (fmap unTy2) ddfs) (fromRANDataCon dcon) of
                0 -> M.empty
                n -> let -- Random access nodes occur immediately after the tag
                         ind_vars = L.map fst $ L.take n vlocs1
                         -- Everything else is a regular consturctor field,
                         -- which depends on some random access node
                         data_fields = reverse $ L.take n (reverse vlocs1)
                         (vars, var_locargs) = unzip data_fields
                         var_locs = map (unwrapLocVar . toLocVar) var_locargs
                     in M.fromList $ zip vars (zip var_locs ind_vars)
        in go field_cur vlocs1 tys1 ran_mp denv1 (M.insert field_cur (MkTy2 CursorTy) tenv1)
      where
        go :: Var -> [(Var, LocArg)] -> [Ty2] -> M.Map Var (Var,Var) -> DepEnv -> TyEnv Var Ty2 -> PassM Exp3
        go cur vlocs tys indirections_env denv tenv = do
          case (vlocs, tys) of
            ([], []) -> processRhs denv tenv
            ((v,locarg):rst_vlocs, (MkTy2 ty):rst_tys) ->
              let loc = toLocVar locarg
                  locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of 
                                Just v' -> v' 
                                Nothing -> error "cursorizeLet: unexpected location variable"
               in case ty of
                -- The random access pointer
                -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
{-
                CursorTy -> do
                  tmp <- gensym "readcursor_shortcut"
                  let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [CursorTy, CursorTy])),
                                                   (loc     , MkTy2 CursorTy),
                                                   (v       , MkTy2 CursorTy),
                                                   (toEndV v, MkTy2 CursorTy)])
                              tenv

                      binds = [(tmp     , [], ProdTy [CursorTy, CursorTy], Ext $ ReadCursor cur),
                               (loc     , [], CursorTy, VarE cur),
                               (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets binds bod
-}

                CursorTy -> do
                  tmp <- gensym "readcursor_shortcut"
                  let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                   (locs_var , MkTy2 CursorTy),
                                                   (v       , MkTy2 CursorTy),
                                                   (toEndV v, MkTy2 CursorTy),
                                                   (toTagV v, MkTy2 IntTy),
                                                   (toEndFromTaggedV v, MkTy2 CursorTy)])
                              tenv
                      read_cursor = Ext (ReadTaggedCursor cur)
                      binds = [(tmp     , [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                               (locs_var , [], CursorTy, VarE cur),
                               (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                               (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                               (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))]
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets binds bod


                -- Int, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v locs_var tenv
                  let loc_bind = case M.lookup v indirections_env of
                                   Nothing ->
                                     (locs_var,[],CursorTy, VarE cur)
                                   -- Read this using a random access node
                                   Just (_var_loc, ind_var) ->
                                     (locs_var,[],CursorTy, VarE ind_var)
                      binds' = loc_bind:binds
                      tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                VectorTy el_ty -> do
                  tmp <- gensym "read_vec_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                                   (v       , MkTy2 (VectorTy el_ty)),
                                                   (toEndV v, MkTy2 CursorTy)])
                              tenv
                      ty'   = stripTyLocs ty
                      binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadVector locs_var (stripTyLocs el_ty)),
                               (v       , [], ty'     , ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      loc_bind = case M.lookup v indirections_env of
                                   Nothing ->
                                     (locs_var, [], CursorTy, VarE cur)
                                   Just (_var_loc, ind_var) ->
                                     (locs_var, [], CursorTy, VarE ind_var)
                      binds' = loc_bind : binds
                      tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                ListTy el_ty -> do
                  tmp <- gensym "read_list_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                                   (v       , MkTy2 (ListTy el_ty)),
                                                   (toEndV v, MkTy2 CursorTy)])
                              tenv
                      ty'   = stripTyLocs ty
                      binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadList locs_var (stripTyLocs el_ty)),
                               (v       , [], ty'     , ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      loc_bind = case M.lookup v indirections_env of
                                   Nothing ->
                                     (locs_var, [], CursorTy, VarE cur)
                                   Just (_var_loc, ind_var) ->
                                     (locs_var, [], CursorTy, VarE ind_var)
                      binds' = loc_bind : binds
                      tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                PackedTy{} -> do
                  let tenv' = M.union (M.fromList [ (locs_var, MkTy2 CursorTy)
                                                  , (v,   MkTy2 CursorTy) ])
                              tenv
                      loc_bind = case M.lookup v indirections_env of
                                   -- This is the first packed value. We can unpack this.
                                   Nothing ->
                                     (locs_var, [], CursorTy, VarE cur)
                                   -- We need to access this using a random access node
                                   Just (_var_loc, ind_var) ->
                                     (locs_var, [], CursorTy, VarE ind_var)
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets [ loc_bind, (v, [], CursorTy, VarE locs_var) ] bod

                _ -> error $ "unpackWitnAbsRAN: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackWitnAbsRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

    -- We have access to all fields in this constructor, and can create
    -- bindings for everything. We begin by unpacking the random access nodes.
    unpackWithRelRAN :: Var -> PassM Exp3
    unpackWithRelRAN field_cur =
        -- ran_mp is a map from a variable to a tuple containing it's location and
        -- the RAN field it depends on. Consider this constructor:
        --
        --     (Node* [(ran_y3, loc_ran_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)] ...),
        --
        -- it will be the map:
        --
        --     (y3 -> (loc_y3, ran_y3))
        let ran_mp =
              case numRANsDataCon (M.map (fmap unTy2) ddfs) (fromRANDataCon dcon) of
                0 -> M.empty
                n -> let -- Random access nodes occur immediately after the tag
                         inds = L.take n $ L.drop 1 vlocs1
                         -- Everything else is a regular consturctor field,
                         -- which depends on some random access node
                         data_fields = reverse $ L.take n (reverse vlocs1)
                         (vars, var_locargs) = unzip data_fields
                         var_locs = map (\lc_arg -> case (M.lookup (fromLocVarToFreeVarsTy (toLocVar lc_arg)) freeVarToVarEnv) of 
                                                                                      Just v' -> v' 
                                                                                      Nothing -> error "cursorizeLet: unexpected location variable" 
                          
                                        ) var_locargs
                     in M.fromList $ zip vars (zip var_locs (map (\(x,y) -> (x,(unwrapLocVar . toLocVar) y)) inds))
        in go field_cur vlocs1 tys1 ran_mp denv1 (M.insert field_cur (MkTy2 CursorTy) tenv1)
      where
        go :: Var -> [(Var, LocArg)] -> [Ty2] -> M.Map Var (Var,(Var,Var)) -> DepEnv -> TyEnv Var Ty2 -> PassM Exp3
        go cur vlocs tys indirections_env denv tenv = do
          case (vlocs, tys) of
            ([], []) -> processRhs denv tenv
            ((v,locarg):rst_vlocs, (MkTy2 ty):rst_tys) ->
              let loc = toLocVar locarg
                  locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of 
                                Just v' -> v' 
                                Nothing -> error "cursorizeLet: unexpected location variable"
               in case ty of
                -- Int, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v locs_var tenv
                  let loc_bind = case M.lookup v indirections_env of
                                   -- This appears before the first packed field. Unpack it
                                   -- in the usual way.
                                   Nothing ->
                                     (locs_var,[],CursorTy, VarE cur)
                                   -- We need to read this using a random access node
                                   Just (_var_loc, (ind_var, ind_loc)) ->
                                     (locs_var,[],CursorTy, Ext $ AddCursor ind_loc (VarE ind_var))
                      binds' = loc_bind:binds
                      tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                PackedTy{} -> do
                  tmp_loc <- gensym "loc"
                  let tenv' = M.union (M.fromList [ (locs_var, MkTy2 CursorTy)
                                                  , (v,   MkTy2 CursorTy) ])
                              tenv
                      loc_binds = case M.lookup v indirections_env of
                                    -- This is the first packed value. We can unpack this.
                                    Nothing ->
                                      [(locs_var, [], CursorTy, VarE cur)]
                                    -- We need to access this using a random access node
                                    Just (_var_loc, (ind_var, ind_loc)) ->
                                      [ (tmp_loc,[],CursorTy, Ext $ AddCursor ind_loc (VarE ind_var))
                                      , (locs_var,[],CursorTy, Ext $ AddCursor tmp_loc (LitE 8)) ]
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets  (loc_binds ++ [(v, [], CursorTy, VarE locs_var)]) bod

                _ -> error $ "unpackWithRelRAN: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackWithRelRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

    -- Generate bindings for unpacking int fields. A convenient
    scalarBinds :: OldTy2 -> Var -> Var -> TyEnv Var Ty2 -> PassM (TyEnv Var Ty2, [(Var, [()], Ty3, Exp3)])
    scalarBinds ty v loc tenv = do
      tmp <- gensym "read_scalar_tuple"
      -- Note that the location is not added to the type environment here.
      -- The caller of this fn will do that later, depending on whether we're
      -- binding the location now or later via DepEnv.
      let s     = mkScalar ty
          tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [ty, CursorTy])),
                                       (v       , MkTy2 ty),
                                       (toEndV v, MkTy2 CursorTy)])
                  tenv

          ty'   = stripTyLocs ty

          binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadScalar s loc),
                   (v       , [], ty'     , ProjE 0 (VarE tmp)),
                   (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
      return (tenv', binds)

giveStarts :: OldTy2 -> Exp3 -> Exp3
giveStarts ty e =
  case ty of
    PackedTy{} -> mkProj 0 e
    -- NOTE : mkProj . MkProdE == id
    ProdTy tys -> MkProdE $ zipWith (\ ty' n -> giveStarts ty' (mkProj n e)) tys [0..]
    _ -> e


projValTy :: (Out a) => UrTy a -> UrTy a
projValTy = projTy 0

projEndsTy :: (Out a) => UrTy a -> UrTy a
projEndsTy = projTy 1


-- -- | Bindings for a letregion
-- regionToBinds :: M.Map FreeVarsTy Var -> Bool -> Region -> RegionSize -> PassM [(Var, [()], Ty3, Exp3)]
-- regionToBinds freeVarToVarEnv for_parallel_allocs r sz = do
--   case r of
--     VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
--     GlobR v mul -> do 
--                    let mul' = go mul
--                    let endv = toEndV v
--                    if for_parallel_allocs
--                    then return $ [ (v       , [], CursorTy, Ext (NewParBuffer mul')) , ((endv), [], CursorTy, Ext (EndOfBuffer mul'))]
--                    else return $ [ (v       , [], CursorTy, Ext (NewBuffer mul'))
--                                  , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
--     DynR v mul  -> do 
--                    let mul' = go mul
--                    if for_parallel_allocs
--                    then return $ [ (v       , [], CursorTy, Ext$ ScopedParBuffer mul')
--                                  , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul')]
--                    else return $ [ (v       , [], CursorTy, Ext$ ScopedBuffer mul')
--                                  , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul')]
--     -- TODO: docs
--     MMapR _v    -> return $ []
    
--     -- TODO: SoA Region
--     SoAR dcreg fieldRegs -> do 
--                             dcreg_binds <- regionToBinds freeVarToVarEnv for_parallel_allocs dcreg sz
--                             field_binds <- concatMapM (\(key, field_reg) -> regionToBinds freeVarToVarEnv for_parallel_allocs field_reg sz) fieldRegs
--                             -- Make the cursor array
--                             let reg_to_reg_var = regionToVar r
--                             regions_var <- case (M.lookup (fromRegVarToFreeVarsTy reg_to_reg_var) freeVarToVarEnv) of 
--                                                 Just v -> return $ v
--                                                 Nothing -> gensym "reg_ptr"
--                             field_reg_vars <- mapM (\(key, field_reg) -> case (M.lookup (fromRegVarToFreeVarsTy (regionToVar field_reg)) freeVarToVarEnv) of 
--                                                                                       Just v -> v
--                                                                                       Nothing -> case field_reg of 
--                                                                                                     VarR v -> return $ v
--                                                                                                     GlobR v _ -> return $ v
--                                                                                                     DynR v _ -> return $ v
--                                                                                                     MMapR v -> return $ v
--                                                                                                     SoAR _ _ -> gensym "reg_ptr"
--                                                    ) fieldRegs
--                               dc_reg_var <- case (M.lookup (fromRegVarToFreeVarsTy (regionToVar dcreg)) freeVarToVarEnv) of 
--                                                 Just v -> return $ v
--                                                 Nothing -> case dcreg of 
--                                                                  VarR v -> return $ v
--                                                                  GlobR v _ -> return $ v
--                                                                  DynR v _ -> return $ v
--                                                                  MMapR v -> return $ v
--                                                                  SoAR _ _ -> error "data constructor region cannot be SoA."
--                               let make_cur_array_bind = (regions_var, [], CursorArrayTy (1 + length (field_reg_vars)), Ext $ MakeCursorArray (1 + length (field_reg_vars)) ([dc_reg_var] ++ field_reg_vars))
--                              in return $ dcreg_binds ++ field_binds ++ [make_cur_array_bind]

--  where
--   go mul =
--     case sz of
--       BoundedSize 0 -> mul
--       BoundedSize x -> Bounded x
--       Undefined     -> mul

-- regionToBinds :: M.Map FreeVarsTy Var -> Bool -> Region -> RegionSize -> PassM ([(Var, [()], Ty3, Exp3)], M.Map FreeVarsTy Var)
-- regionToBinds freeVarToVarEnv for_parallel_allocs r sz = do
--   case r of
--     VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
--     GlobR v mul -> do 
--                    let mul' = go mul
--                    let endv = toEndV v
--                    let bnds = if for_parallel_allocs
--                               then [ (v       , [], CursorTy, Ext (NewParBuffer mul')) , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
--                               else [ (v       , [], CursorTy, Ext (NewBuffer mul'))
--                                  , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
--                    return (bnds, freeVarToVarEnv)
--     DynR v mul  -> do 
--                    let mul' = go mul
--                    let bnds = if for_parallel_allocs
--                               then [ (v       , [], CursorTy, Ext (ScopedParBuffer mul'))
--                                  , (toEndV v, [], CursorTy, Ext (EndOfBuffer mul'))]
--                               else [ (v       , [], CursorTy, Ext (ScopedBuffer mul'))
--                                  , (toEndV v, [], CursorTy, Ext (EndOfBuffer mul'))]
--                    return (bnds, freeVarToVarEnv)
--     -- TODO: docs
--     MMapR _v    -> return ([], freeVarToVarEnv)
    
--     -- TODO: SoA Region
--     SoAR dcreg fieldRegs -> do 
--                             (dcreg_binds, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv for_parallel_allocs dcreg sz
--                             field_binds_pairs <- fmap concat $ mapM (\(key, field_reg) -> regionToBinds freeVarToVarEnv for_parallel_allocs field_reg sz) fieldRegs
--                             let field_binds = map fst field_binds_pairs
--                             let field_new_maps = map snd field_binds_pairs 
--                             -- Make the cursor array
--                             let reg_to_reg_var = regionToVar r
--                             regions_var <- case M.lookup (fromRegVarToFreeVarsTy reg_to_reg_var) freeVarToVarEnv of 
--                                                 Just v -> return v
--                                                 Nothing -> gensym "reg_ptr"
--                             let freeVarToVarEnv'' = M.insert (fromRegVarToFreeVarsTy reg_to_reg_var) regions_var freeVarToVarEnv'
--                             field_reg_keys_vars <- mapM (\(key, field_reg) -> do 
--                                                                               case M.lookup (fromRegVarToFreeVarsTy (regionToVar field_reg)) freeVarToVarEnv of 
--                                                                                       Just v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                       Nothing -> case field_reg of 
--                                                                                                     VarR v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                     GlobR v _ -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                     DynR v _ -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                     MMapR v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                      SoAR _ _ -> do 
--                                                                                                                  new_name <- gensym "reg_ptr" 
--                                                                                                                  return (fromRegVarToFreeVarsTy (regionToVar field_reg), new_name)
--                                                    ) fieldRegs
--                             let field_reg_keys = map fst field_reg_keys_vars
--                             let field_reg_vars = map snd field_reg_keys_vars
--                             let freeVarToVarEnv''' = foldr (\(key, var) acc -> M.insert key var acc) freeVarToVarEnv'' field_reg_keys_vars
--                             dc_reg_var <- case M.lookup (fromRegVarToFreeVarsTy (regionToVar dcreg)) freeVarToVarEnv of 
--                                                 Just v -> return v
--                                                 Nothing -> case dcreg of 
--                                                                  VarR v -> return v
--                                                                  GlobR v _ -> return v
--                                                                  DynR v _ -> return v
--                                                                  MMapR v -> return v
--                                                                  SoAR _ _ -> error "data constructor region cannot be SoA."
--                             let freeVarToVarEnv'''' = M.insert (fromRegVarToFreeVarsTy (regionToVar dcreg)) dc_reg_var freeVarToVarEnv'''
--                             let make_cur_array_bind = (regions_var, [], CursorArrayTy (1 + length field_reg_vars), Ext $ MakeCursorArray (1 + length field_reg_vars) ([dc_reg_var] ++ field_reg_vars))
--                             return (dcreg_binds ++ field_binds ++ [make_cur_array_bind], freeVarToVarEnv'''')

--  where
--   go mul =
--     case sz of
--       BoundedSize 0 -> mul
--       BoundedSize x -> Bounded x
--       Undefined     -> mul

regionToBinds :: M.Map FreeVarsTy Var -> Bool -> Region -> RegionSize -> PassM ([(Var, [()], Ty3, Exp3)], M.Map FreeVarsTy Var)
regionToBinds freeVarToVarEnv for_parallel_allocs r sz = do
  case r of
    VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
    GlobR v mul -> do 
                   let mul' = go mul
                   let endv = toEndV v
                   let bnds = if for_parallel_allocs
                              then [ (v       , [], CursorTy, Ext (NewParBuffer mul')) , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
                              else [ (v       , [], CursorTy, Ext (NewBuffer mul'))
                                 , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
                   return (bnds, freeVarToVarEnv)
    DynR v mul  -> do 
                   let mul' = go mul
                   let bnds = if for_parallel_allocs
                              then [ (v       , [], CursorTy, Ext (ScopedParBuffer mul'))
                                 , (toEndV v, [], CursorTy, Ext (EndOfBuffer mul'))]
                              else [ (v       , [], CursorTy, Ext (ScopedBuffer mul'))
                                 , (toEndV v, [], CursorTy, Ext (EndOfBuffer mul'))]
                   return (bnds, freeVarToVarEnv)
    -- TODO: docs
    MMapR _v    -> return ([], freeVarToVarEnv)
    
    -- TODO: SoA Region
    SoAR dcreg fieldRegs -> do 
                            (dcreg_binds, _freeVarToVarEnv) <- regionToBinds freeVarToVarEnv for_parallel_allocs dcreg sz
                            field_binds_pairs <- mapM (\(key, field_reg) -> regionToBinds _freeVarToVarEnv for_parallel_allocs field_reg sz) fieldRegs
                            let field_binds = concatMap fst field_binds_pairs
                            let field_new_maps = map snd field_binds_pairs 
                            let _freeVarToVarEnv' = foldr (\m acc -> M.union m acc) freeVarToVarEnv field_new_maps
                            let freeVarToVarEnv' = M.union _freeVarToVarEnv' _freeVarToVarEnv
                            -- Make the cursor array
                            let reg_to_reg_var = regionToVar r
                            regions_var <- case M.lookup (fromRegVarToFreeVarsTy reg_to_reg_var) freeVarToVarEnv' of 
                                                Just v -> return v
                                                Nothing -> gensym "reg_ptr"
                            let freeVarToVarEnv'' = M.insert (fromRegVarToFreeVarsTy reg_to_reg_var) regions_var freeVarToVarEnv'
                            field_reg_keys_vars <- mapM (\(key, field_reg) -> do 
                                                                              case M.lookup (fromRegVarToFreeVarsTy (regionToVar field_reg)) freeVarToVarEnv'' of 
                                                                                      Just v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
                                                                                      Nothing -> case field_reg of 
                                                                                                    VarR v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
                                                                                                    GlobR v _ -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
                                                                                                    DynR v _ -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
                                                                                                    MMapR v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
                                                                                                    SoAR _ _ -> do 
                                                                                                                 new_name <- gensym "reg_ptr" 
                                                                                                                 return (fromRegVarToFreeVarsTy (regionToVar field_reg), new_name)
                                                   ) fieldRegs
                            let field_reg_keys = map fst field_reg_keys_vars
                            let field_reg_vars = map snd field_reg_keys_vars
                            let field_end_reg_keys = map (\(R r) -> toEndVRegVar r) field_reg_keys
                            freeVarToVarEnv''' <- foldrM (\key acc -> insertRegInVarEnv key acc) freeVarToVarEnv'' field_end_reg_keys 
                            let field_end_reg_vars = map (\key -> case (M.lookup (fromRegVarToFreeVarsTy key) freeVarToVarEnv''') of 
                                                                    Just v -> v
                                                                    Nothing -> error "cursorizeExp: regionToBinds: SoAR: unexpected end of region variable"
                                                         ) field_end_reg_keys
                            let freeVarToVarEnv'''' = foldr (\(key, var) acc -> M.insert key var acc) freeVarToVarEnv''' field_reg_keys_vars
                            dc_reg_var <- case M.lookup (fromRegVarToFreeVarsTy (regionToVar dcreg)) freeVarToVarEnv'''' of 
                                                Just v -> return v
                                                Nothing -> case dcreg of 
                                                                 VarR v -> return v
                                                                 GlobR v _ -> return v
                                                                 DynR v _ -> return v
                                                                 MMapR v -> return v
                                                                 SoAR _ _ -> error "data constructor region cannot be SoA."
                            let freeVarToVarEnv''''' = M.insert (fromRegVarToFreeVarsTy (regionToVar dcreg)) dc_reg_var freeVarToVarEnv''''
                            let dc_reg_end_var = toEndVRegVar (regionToVar dcreg)
                            freeVarToVarEnv'''''' <- insertRegInVarEnv dc_reg_end_var freeVarToVarEnv'''''
                            let dc_reg_end_var_name = case (M.lookup (fromRegVarToFreeVarsTy dc_reg_end_var) freeVarToVarEnv'''''') of 
                                                            Just v -> v
                                                            Nothing -> error "cursorizeExp: regionToBinds: SoAR: unexpected end of region variable"
                            let end_soa_reg = toEndVRegVar (regionToVar r)
                            freeVarToVarEnv''''''' <- insertRegInVarEnv end_soa_reg freeVarToVarEnv''''''
                            let end_soa_reg_name = case (M.lookup (fromRegVarToFreeVarsTy end_soa_reg) freeVarToVarEnv''''''') of 
                                                            Just v -> v
                                                            Nothing -> error "cursorizeExp: regionToBinds: SoAR: unexpected end of region variable"
                            let make_cur_array_bind = (regions_var, [], CursorArrayTy (1 + length field_reg_vars), Ext $ MakeCursorArray (1 + length field_reg_vars) ([dc_reg_var] ++ field_reg_vars))
                            let make_end_cur_array_bind = (end_soa_reg_name, [], CursorArrayTy (1 + length field_end_reg_vars), Ext $ MakeCursorArray (1 + length field_end_reg_vars) ([dc_reg_end_var_name] ++ field_end_reg_vars))
                            return (dcreg_binds ++ field_binds ++ [make_cur_array_bind] ++ [make_end_cur_array_bind], freeVarToVarEnv''''''')

 where
  go mul =
    case sz of
      BoundedSize 0 -> mul
      BoundedSize x -> Bounded x
      Undefined     -> mul


isBound :: Var -> TyEnv Var Ty2 -> Bool
isBound l m = M.member l m
               
-- ================================================================================
--                         Dilation Conventions
-- ================================================================================
-- Everything to do with dilation.  It should be possible to change
-- the dilated format by changing only this section.


-- | If an expression `e` returns type `T`, then a dilated version of
-- `e` returns a tuple (T,Cursors), where cursors contains a flat
-- record of end-cursors corresponding exactly to all the components
-- of T which are PackedTy.
--
newtype DiExp ex = Di ex
  deriving (Generic, Show, Read, Eq, Ord)
--type DiExp = Exp

instance (Out ex) => Out (DiExp ex)

onDi :: (ex -> ex) -> DiExp ex -> DiExp ex
onDi f (Di x) = Di (f x)

fromDi :: DiExp ex -> ex
fromDi (Di x) = x


-- | Project the cursor package from a dilated expression, contains pointers
-- to all the ENDs.
projEnds :: DiExp Exp3 -> Exp3
projEnds (Di e) = mkProj 1 e

-- | Project the original value from a dilated expression.
projVal :: DiExp Exp3 -> Exp3
projVal (Di e) = mkProj 0 e

-- | Constructor that combines a regular expression with a list of
-- corresponding end cursors.
mkDi :: Exp3 -> [Exp3] -> DiExp Exp3
mkDi x []  = Di $ MkProdE [x,MkProdE []]
mkDi x [o] = Di $ MkProdE [x, o]
mkDi x ls  = Di $ MkProdE [x, MkProdE ls]

curDict :: UrTy a -> UrTy a
curDict (SymDictTy ar _ty) = SymDictTy ar CursorTy
curDict ty = ty
