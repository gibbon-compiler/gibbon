{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE QuasiQuotes        #-}
{-# LANGUAGE TemplateHaskell    #-}

-- | The final pass of the compiler: generate C code.

module Gibbon.Passes.Codegen
  ( codegenProg, harvestStructTys, makeName, rewriteReturns ) where

import           Control.Monad
import           Data.Bifunctor (first)
import           Data.Int
import           Data.Loc
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.List as L
import qualified Data.Set as S
import           Language.C.Quote.C (cdecl, cedecl, cexp, cfun, cparam, csdecl, cstm, cty)
import qualified Language.C.Quote.C as C
import qualified Language.C.Syntax as C

import qualified Safe as Sf
import           Prelude hiding (init)
import           Text.PrettyPrint.Mainland
import           Text.PrettyPrint.Mainland.Class

import           Gibbon.Common
import qualified Gibbon.Language as GL
import           Gibbon.DynFlags
import           Gibbon.L2.Syntax ( Multiplicity(..) )
import           Gibbon.L4.Syntax
import qualified Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------


-- | Harvest all struct tys.  All product types used anywhere in the program.
harvestStructTys :: Prog -> S.Set [Ty]
harvestStructTys (Prog _ _ funs mtal) =
    S.delete [] $
    S.map (\tys -> filter (\ty -> ty /= (ProdTy [])) tys) $
    (S.union tys0 tys1)
  where
  tys00 = concatMap allTypes allTails

  tys0 :: S.Set [Ty]
  tys0 = findAllProds tys00

  tys1 :: S.Set [Ty]
  -- All types mentioned in function arguments and returns:
  tys1 = S.fromList [ tys | fn <- funs, ProdTy tys <- funTys fn ]
  -- structs f = makeStructs $ S.toList $ harvestStructTys prg

  funTys :: FunDecl -> [Ty]
  funTys FunDecl{funArgs = args, funRetTy = ty} = ty : (map snd args)

  allTails = (case mtal of
                Just (PrintExp t) -> [t]
                Nothing -> []) ++
             map funBody funs

  -- We may have nested products; this finds everything:
  findAllProds :: [Ty] -> S.Set [Ty]
  findAllProds = go
    where
      go []     = S.empty
      go (t:ts) =
       case t of
         ProdTy [] -> go ts
         ProdTy ls -> S.insert ls $ S.union (go ls) (go ts)
         VectorTy ty -> S.insert [VectorTy ty] $ S.union (go [ty])(go ts)
         ListTy ty -> S.insert [ListTy ty] $ S.union (go [ty])(go ts)
         PDictTy k v -> S.insert [PDictTy k v] $ S.union (go [k, v]) (go ts)
         _ -> go ts

  -- This finds all types that maybe grouped together as a ProdTy:
  allTypes :: Tail -> [Ty]
  allTypes = go
   where
    go tl =
     case tl of
       EndOfMain -> []
       (RetValsT _)  -> []
       (AssnValsT ls bod_maybe) ->
         case bod_maybe of
           Just bod -> ProdTy (map (\(_,x,_) -> x) ls) : go bod
           Nothing  -> [ProdTy (map (\(_,x,_) -> x) ls)]
       -- This creates a demand for a struct return, but it is covered
       -- by the fun signatures already:
       (LetCallT _ binds _ _  bod) -> ProdTy (map snd binds) : go bod
       -- INVARIANT: This does not create a struct:
       -- But just in case it does in the future, we add it:
       (LetPrimCallT binds prm _ bod) ->
         let rst = go bod in
         case prm of
           VAllocP elty  -> VectorTy elty : rst
           VFreeP elty   -> VectorTy elty : rst
           VFree2P elty  -> VectorTy elty : rst
           VLengthP elty -> VectorTy elty : rst
           VNthP   elty  -> VectorTy elty : rst
           VSliceP elty  -> VectorTy elty : rst
           InplaceVUpdateP elty -> VectorTy elty : rst
           VConcatP elty -> VectorTy elty : rst
           VSortP elty   -> VectorTy elty : rst
           InplaceVSortP _elty  -> voidTy : rst
           VMergeP elty -> VectorTy elty : rst
           LLAllocP elty -> ListTy elty : rst
           LLIsEmptyP elty -> ListTy elty : rst
           LLConsP elty -> ListTy elty : rst
           LLHeadP elty -> ListTy elty : rst
           LLTailP elty -> ListTy elty : rst
           LLFreeP elty -> ListTy elty : rst
           LLFree2P elty -> ListTy elty : rst
           LLCopyP elty -> ListTy elty : rst
           PDictAllocP k v -> PDictTy k v : rst
           PDictInsertP k v -> PDictTy k v : rst
           PDictLookupP k v -> PDictTy k v : rst
           PDictHasKeyP k v -> PDictTy k v : rst
           PDictForkP k v -> PDictTy k v : rst
           PDictJoinP k v -> PDictTy k v : rst
           ReadArrayFile _ elty -> VectorTy elty : rst
           _ -> ProdTy (map snd binds) : rst
       (LetTrivT (_,ty,_) bod)     -> ty : go bod
       -- This should not create a struct.  Again, we add it just for the heck of it:
       (LetIfT binds (_,a,b) bod)  -> ProdTy (map snd binds) : go a ++ go b ++ go bod
       (LetTimedT _ binds rhs bod) -> ProdTy (map snd binds) : go rhs ++ go bod
       (LetArenaT _ bod)          -> ProdTy [ArenaTy] : go bod

       -- These are precisely for operating on structs:
       (LetUnpackT binds _ bod)    -> ProdTy (map snd binds) : go bod
       (LetAllocT _ vals bod)      -> ProdTy (map fst vals) : go bod
       (LetAvailT _ bod)           -> go bod
       (ForLoopT _ _ loopBody bod) -> go loopBody ++ go bod
       (WhileCursorT _ loopBody bod) -> go loopBody ++ go bod
       (WhileCursorEndT _ _ loopBody bod) -> go loopBody ++ go bod

       (IfT _ a b) -> go a ++ go b
       ErrT{} -> []
       (Switch _ _ (IntAlts ls) b) -> concatMap (go . snd) ls ++ concatMap go (maybeToList b)
       (Switch _ _ (TagAlts ls) b) -> concatMap (go . snd) ls ++ concatMap go (maybeToList b)
       (TailCall _ _)    -> []
       (Goto _) -> []

-- | Free vars in an L4 tail. We only need a conservative approximation here
-- for resetting timed packed-output state between iterate runs.
tailFreeVars :: Tail -> S.Set Var
tailFreeVars tl =
  case tl of
    RetValsT trvs ->
      S.unions (map trivFreeVars trvs)
    EndOfMain ->
      S.empty
    AssnValsT upds bod_maybe ->
      S.fromList [v | (v, _, _) <- upds]
        `S.union` S.unions [trivFreeVars trv | (_, _, trv) <- upds]
        `S.union` maybe S.empty tailFreeVars bod_maybe
    LetCallT {binds, rator, rands, bod} ->
      (S.insert rator (S.unions (map trivFreeVars rands) `S.union` tailFreeVars bod))
        `S.difference` S.fromList (map fst binds)
    LetPrimCallT {binds, rands, bod} ->
      (S.unions (map trivFreeVars rands) `S.union` tailFreeVars bod)
        `S.difference` S.fromList (map fst binds)
    LetTrivT {bnd = (v, _, trv), bod} ->
      trivFreeVars trv `S.union` (tailFreeVars bod `S.difference` S.singleton v)
    LetIfT {binds, ife = (tst, con, els), bod} ->
      trivFreeVars tst
        `S.union` ((tailFreeVars con `S.union` tailFreeVars els `S.union` tailFreeVars bod)
                    `S.difference` S.fromList (map fst binds))
    LetUnpackT {binds, ptr, bod} ->
      S.insert ptr (tailFreeVars bod `S.difference` S.fromList (map fst binds))
    LetAllocT {lhs, vals, bod} ->
      (S.unions [trivFreeVars trv | (_, trv) <- vals] `S.union` tailFreeVars bod)
        `S.difference` S.singleton lhs
    LetAvailT {bod} ->
      tailFreeVars bod
    ForLoopT {idx, bound, loopBody, bod} ->
      trivFreeVars bound
        `S.union` ((tailFreeVars loopBody `S.difference` S.singleton idx)
                    `S.union` tailFreeVars bod)
    WhileCursorT {ref, loopBody, bod} ->
      S.singleton ref `S.union` tailFreeVars loopBody `S.union` tailFreeVars bod
    WhileCursorEndT {ref, endRef, loopBody, bod} ->
      S.fromList [ref, endRef] `S.union` tailFreeVars loopBody `S.union` tailFreeVars bod
    IfT {tst, con, els} ->
      trivFreeVars tst `S.union` tailFreeVars con `S.union` tailFreeVars els
    ErrT _ ->
      S.empty
    LetTimedT {binds, timed, bod} ->
      (tailFreeVars timed `S.union` tailFreeVars bod)
        `S.difference` S.fromList (map fst binds)
    Switch lbl trv alts def ->
      S.insert lbl $
        trivFreeVars trv
          `S.union` altsFreeVars alts
          `S.union` maybe S.empty tailFreeVars def
    TailCall f trvs ->
      S.insert f (S.unions (map trivFreeVars trvs))
    Goto lbl ->
      S.singleton lbl
    LetArenaT {lhs, bod} ->
      tailFreeVars bod `S.difference` S.singleton lhs
  where
    altsFreeVars :: Alts -> S.Set Var
    altsFreeVars alts =
      case alts of
        TagAlts ls -> S.unions (map (tailFreeVars . snd) ls)
        IntAlts ls -> S.unions (map (tailFreeVars . snd) ls)

trivFreeVars :: Triv -> S.Set Var
trivFreeVars trv =
  case trv of
    VarTriv v ->
      S.singleton v
    IntTriv{} ->
      S.empty
    CharTriv{} ->
      S.empty
    FloatTriv{} ->
      S.empty
    BoolTriv{} ->
      S.empty
    TagTriv{} ->
      S.empty
    SymTriv{} ->
      S.empty
    ProdTriv trvs ->
      S.unions (map trivFreeVars trvs)
    ProjTriv _ trv1 ->
      trivFreeVars trv1
    IndexCursorArrayTriv _ trv1 ->
      trivFreeVars trv1
    UninitTriv{} ->
      S.empty
    SizeOf{} ->
      S.empty

needsIterReset :: Ty -> Bool
needsIterReset ty =
  case ty of
    MutCursorTy -> True
    CursorArrayTy{} -> True
    _ -> False

timedStateVars :: M.Map Var Ty -> Tail -> [(Var, Ty)]
timedStateVars venv _rhs =
  [ (v, ty)
  | (v, ty) <- M.toList venv
  , needsIterReset ty
  ]

sortFns :: Prog -> S.Set Var
sortFns (Prog _ _ funs mtal) = foldl go S.empty allTails
  where
    allTails = (case mtal of
                Just (PrintExp t) -> [t]
                Nothing -> []) ++
             map funBody funs

    go acc tl =
      case tl of
        EndOfMain -> acc
        RetValsT{} -> acc
        AssnValsT _ mb_bod -> case mb_bod of
                                Just bod -> go acc bod
                                Nothing  -> acc
        LetCallT{bod} -> go acc bod
        LetPrimCallT{prim,bod,rands} ->
          case prim of
            VSortP{} ->
              let [_,VarTriv fp] = rands
              in go (S.insert fp acc) bod
            InplaceVSortP{} ->
              let [_,VarTriv fp] = rands
              in go (S.insert fp acc) bod
            _ -> go acc bod
        LetTrivT{bod}   -> go acc bod
        LetIfT{ife,bod} ->
          let (_,a,b) = ife
          in go (go (go acc a) b) bod
        LetUnpackT{bod} -> go acc bod
        LetAllocT{bod}  -> go acc bod
        LetAvailT{bod}  -> go acc bod
        ForLoopT{loopBody,bod} -> go (go acc loopBody) bod
        WhileCursorT{loopBody,bod} -> go (go acc loopBody) bod
        WhileCursorEndT{loopBody,bod} -> go (go acc loopBody) bod
        IfT{con,els}    -> go (go acc con) els
        ErrT{} -> acc
        LetTimedT{timed,bod} -> go (go acc timed) bod
        Switch _ _ alts mb_tl ->
          let acc1 = case mb_tl of
                       Nothing -> acc
                       Just tl -> go acc tl
          in case alts of
               TagAlts ls -> foldr (\(_,b) ac -> go ac b) acc1 ls
               IntAlts ls -> foldr (\(_,b) ac -> go ac b) acc1 ls
        TailCall{}     -> acc
        Goto{}         -> acc
        LetArenaT{bod} -> go acc bod

--------------------------------------------------------------------------------
-- * C codegen

-- | Compile a program to C code that has the side effect of the
-- "gibbon_main" expression in that program.
codegenProg :: Config -> Prog -> IO String
codegenProg cfg prg@(Prog info_tbl sym_tbl funs mtal) =
      return (hashIncludes ++ pretty 80 (stack (map ppr defs)))
    where
      init_fun_env = foldr (\fn acc -> M.insert (funName fn) (map snd (funArgs fn), funRetTy fn) acc) M.empty funs

      sort_fns = sortFns prg

      defs = fst $ runPassM cfg 0 $ do
        (prots,funs') <- (unzip . concat) <$> mapM codegenFun funs
        main_expr' <- main_expr
        let struct_tys = uniqueDicts $ S.toList $ harvestStructTys prg
        return ((L.nub $ makeStructs struct_tys) ++ prots ++
                [gibTypesEnum, initInfoTable info_tbl, initSymTable sym_tbl] ++
                funs' ++ [main_expr'])

      main_expr :: PassM C.Definition
      main_expr = do
        dflags <- getDynFlags
        let pointer = gopt Opt_Pointer dflags
        let gen_gc = gopt Opt_GenGc dflags
        e <- case mtal of
               -- [2019.06.13]: CSK, Why is codegenTail always called with IntTy?
               Just (PrintExp t) -> codegenTail M.empty M.empty init_fun_env sort_fns t IntTy []
               _ -> pure []
        ret_init <- gensym "init"
        ret_exit <- gensym "exit"
        let init_gib = (if pointer then [ C.BlockStm [cstm| GC_INIT(); |] ] else []) ++
                       [ C.BlockDecl [cdecl| int $id:ret_init = gib_init(argc, argv); |] ]
            exit_gib = [ C.BlockDecl [cdecl| int $id:ret_exit = gib_exit(); |]
                       , C.BlockStm [cstm| return $id:ret_exit; |]
                       ]
            init_info_table = [ C.BlockStm [cstm| info_table_initialize(); |] ]
            init_symbol_table = [ C.BlockStm [cstm| symbol_table_initialize(); |] ]
        let bod = init_gib ++ init_info_table ++ init_symbol_table
                  ++ (if gen_gc then ssDecls else [])
                  ++ e ++ exit_gib
        pure $ C.FuncDef [cfun| int main(int argc, char **argv) { $items:bod } |] noLoc

      codegenFun' :: FunDecl -> PassM C.Func
      codegenFun' FunDecl{funName = nam, funArgs = args, funRetTy = ty, funBody = tal} =
          do dflags <- getDynFlags
             let gen_gc = gopt Opt_GenGc dflags
             let retTy   = codegenTy ty
                 params  = map (\(v,t) -> [cparam| $ty:(codegenTy t) $id:v |]) args
                 init_venv = M.fromList args
             let nam' = if S.member nam sort_fns
                        then varAppend nam (toVar "_original")
                        else nam
             body <- codegenTail init_venv M.empty init_fun_env sort_fns tal ty []
             let body' = (if gen_gc then ssDecls else []) ++ body
             let fun = [cfun| $ty:retTy $id:nam' ($params:params) {
                              $items:body'
                              } |]
             return fun

      -- C's qsort expects a sort function to be of type, (void*  a, void* b) : int.
      -- But there's no way for a user to write a function of this type. So we generate
      -- the function that the user wrote with a different_name, and then codegenSortFn
      -- generates the actual sort function; which reads the values from these void*
      -- pointers and calls the user written one after that.
      codegenSortFn :: FunDecl -> PassM C.Func
      codegenSortFn FunDecl{funName = nam, funArgs = args} = do
        let nam' = varAppend nam (toVar "_original")
            ([v0,v1],[ty0,ty1]) = unzip args
            params     = map (\v -> [cparam| const void* $id:v |]) [v0,v1]
        tmpa <- gensym "fst"
        tmpb <- gensym "snd"
        let bod = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:tmpa = *($ty:(codegenTy ty0) *) $id:v0; |]
                  , C.BlockDecl [cdecl| $ty:(codegenTy ty1) $id:tmpb = *($ty:(codegenTy ty1) *) $id:v1; |]
                  , C.BlockStm  [cstm| return $id:nam'($id:tmpa, $id:tmpb);|]
                  ]
            fun = [cfun| int $id:nam ($params:params) {
                          $items:bod
                       } |]
        return fun

      makeProt :: C.Func -> Bool -> PassM C.InitGroup
      makeProt fn _ispure = do
        dflags <- getDynFlags
        let prot@(C.InitGroup _decl_spec _ _inits _lc) = C.funcProto fn
            _purattr = C.Attr (C.Id "pure" noLoc) [] noLoc
            -- Only add pure annotations if compiling in pointer mode, and if the
            -- --no-pure-annot flag is not passed.
            _pureAnnotOk = not (gopt Opt_No_PureAnnot dflags || gopt Opt_Packed dflags)
        -- if ispure && pureAnnotOk
        -- then return $ C.InitGroup decl_spec [purattr] inits lc
        -- else return prot
        return prot

      codegenFun :: FunDecl -> PassM [(C.Definition, C.Definition)]
      codegenFun fd@FunDecl{funName} =
          do fun <- codegenFun' fd
             prot <- makeProt fun (isPure fd)
             sort_fn <- if S.member funName sort_fns
                        then do
                          fun' <- codegenSortFn fd
                          let prot = C.funcProto fun'
                          pure [(C.DecDef prot noLoc, C.FuncDef fun' noLoc)]
                        else pure []
             return $ [(C.DecDef prot noLoc, C.FuncDef fun noLoc)] ++ sort_fn

      gibTypesEnum =
        let go str = C.CEnum (C.Id (str ++ "_T") noLoc) Nothing noLoc
            decls = map go (builtinFieldTys ++ M.keys info_tbl)
        in [cedecl| typedef enum { $enums:decls } GibDatatype; |]

      hashIncludes =
        "/* Gibbon program. */\n\n" ++
        (if gopt Opt_Int32 (dynflags cfg) then "#define GIBBON_INT32 1\n" else "") ++
        "#include \"gibbon_rts.h\"\n\n\
        \#include <assert.h>\n\
        \#include <stdio.h>\n\
        \#include <stdlib.h>\n\
        \#include <stdint.h>\n\
        \#include <inttypes.h>\n\
        \#include <math.h>\n\
        \#include <stdbool.h>\n\
        \#include <string.h>\n\
        \#include <time.h>\n\
        \#include <alloca.h>\n\
        \#include <sys/mman.h>\n\
        \#include <sys/resource.h>\n\
        \#include <sys/stat.h>\n\
        \#include <unistd.h>\n\
        \#include <fcntl.h>\n\
        \#include <stdarg.h>\n\
        \#include <errno.h>\n\
        \#include <xmmintrin.h>\n\
        \#include <emmintrin.h>\n\
        \#include <uthash.h>\n\n\
        \static inline __m128i gib_vec_broadcast_int64x2(GibInt x) {\n\
        \  return _mm_set1_epi64x((long long) x);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_load_int64x2(GibCursor *ref) {\n\
        \  return _mm_loadu_si128((const __m128i *) (*ref));\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_add_int64x2(__m128i a, __m128i b) {\n\
        \  return _mm_add_epi64(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_sub_int64x2(__m128i a, __m128i b) {\n\
        \  return _mm_sub_epi64(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_mul_int64x2(__m128i a, __m128i b) {\n\
        \  GibInt av[2], bv[2];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi64x(av[1] * bv[1], av[0] * bv[0]);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_div_int64x2(__m128i a, __m128i b) {\n\
        \  GibInt av[2], bv[2];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi64x(av[1] / bv[1], av[0] / bv[0]);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_mod_int64x2(__m128i a, __m128i b) {\n\
        \  GibInt av[2], bv[2];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi64x(av[1] % bv[1], av[0] % bv[0]);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_eq_int64x2(__m128i a, __m128i b) {\n\
        \  GibInt av[2], bv[2];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi64x(av[1] == bv[1] ? -1LL : 0LL, av[0] == bv[0] ? -1LL : 0LL);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_select_int64x2(__m128i mask, __m128i thenv, __m128i elsev) {\n\
        \  return _mm_or_si128(_mm_and_si128(mask, thenv), _mm_andnot_si128(mask, elsev));\n\
        \}\n\
        \\n\
        \static inline void gib_vec_store_int64x2(GibCursor *ref, __m128i v) {\n\
        \  _mm_storeu_si128((__m128i *) (*ref), v);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_broadcast_int32x4(GibInt x) {\n\
        \  return _mm_set1_epi32((int) x);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_load_int32x4(GibCursor *ref) {\n\
        \  return _mm_loadu_si128((const __m128i *) (*ref));\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_add_int32x4(__m128i a, __m128i b) {\n\
        \  return _mm_add_epi32(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_sub_int32x4(__m128i a, __m128i b) {\n\
        \  return _mm_sub_epi32(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_mul_int32x4(__m128i a, __m128i b) {\n\
        \  int32_t av[4], bv[4];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi32(av[3] * bv[3], av[2] * bv[2], av[1] * bv[1], av[0] * bv[0]);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_div_int32x4(__m128i a, __m128i b) {\n\
        \  int32_t av[4], bv[4];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi32(av[3] / bv[3], av[2] / bv[2], av[1] / bv[1], av[0] / bv[0]);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_mod_int32x4(__m128i a, __m128i b) {\n\
        \  int32_t av[4], bv[4];\n\
        \  _mm_storeu_si128((__m128i *) av, a);\n\
        \  _mm_storeu_si128((__m128i *) bv, b);\n\
        \  return _mm_set_epi32(av[3] % bv[3], av[2] % bv[2], av[1] % bv[1], av[0] % bv[0]);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_eq_int32x4(__m128i a, __m128i b) {\n\
        \  return _mm_cmpeq_epi32(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_select_int32x4(__m128i mask, __m128i thenv, __m128i elsev) {\n\
        \  return _mm_or_si128(_mm_and_si128(mask, thenv), _mm_andnot_si128(mask, elsev));\n\
        \}\n\
        \\n\
        \static inline void gib_vec_store_int32x4(GibCursor *ref, __m128i v) {\n\
        \  _mm_storeu_si128((__m128i *) (*ref), v);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_broadcast_sym64x2(GibSym x) {\n\
        \  return _mm_set1_epi64x((long long) x);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_load_sym64x2(GibCursor *ref) {\n\
        \  return _mm_loadu_si128((const __m128i *) (*ref));\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_add_sym64x2(__m128i a, __m128i b) {\n\
        \  return _mm_add_epi64(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_sub_sym64x2(__m128i a, __m128i b) {\n\
        \  return _mm_sub_epi64(a, b);\n\
        \}\n\
        \\n\
        \static inline void gib_vec_store_sym64x2(GibCursor *ref, __m128i v) {\n\
        \  _mm_storeu_si128((__m128i *) (*ref), v);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_broadcast_char8x16(GibChar x) {\n\
        \  return _mm_set1_epi8((char) x);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_load_char8x16(GibCursor *ref) {\n\
        \  return _mm_loadu_si128((const __m128i *) (*ref));\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_add_char8x16(__m128i a, __m128i b) {\n\
        \  return _mm_add_epi8(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_sub_char8x16(__m128i a, __m128i b) {\n\
        \  return _mm_sub_epi8(a, b);\n\
        \}\n\
        \\n\
        \static inline void gib_vec_store_char8x16(GibCursor *ref, __m128i v) {\n\
        \  _mm_storeu_si128((__m128i *) (*ref), v);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_broadcast_bool8x16(GibBool x) {\n\
        \  return _mm_set1_epi8((char) x);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_load_bool8x16(GibCursor *ref) {\n\
        \  return _mm_loadu_si128((const __m128i *) (*ref));\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_add_bool8x16(__m128i a, __m128i b) {\n\
        \  return _mm_add_epi8(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128i gib_vec_sub_bool8x16(__m128i a, __m128i b) {\n\
        \  return _mm_sub_epi8(a, b);\n\
        \}\n\
        \\n\
        \static inline void gib_vec_store_bool8x16(GibCursor *ref, __m128i v) {\n\
        \  _mm_storeu_si128((__m128i *) (*ref), v);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_broadcast_float32x4(GibFloat x) {\n\
        \  return _mm_set1_ps((float) x);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_load_float32x4(GibCursor *ref) {\n\
        \  return _mm_loadu_ps((const float *) (*ref));\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_add_float32x4(__m128 a, __m128 b) {\n\
        \  return _mm_add_ps(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_sub_float32x4(__m128 a, __m128 b) {\n\
        \  return _mm_sub_ps(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_mul_float32x4(__m128 a, __m128 b) {\n\
        \  return _mm_mul_ps(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_div_float32x4(__m128 a, __m128 b) {\n\
        \  return _mm_div_ps(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_eq_float32x4(__m128 a, __m128 b) {\n\
        \  return _mm_cmpeq_ps(a, b);\n\
        \}\n\
        \\n\
        \static inline __m128 gib_vec_select_float32x4(__m128 mask, __m128 thenv, __m128 elsev) {\n\
        \  return _mm_or_ps(_mm_and_ps(mask, thenv), _mm_andnot_ps(mask, elsev));\n\
        \}\n\
        \\n\
        \static inline void gib_vec_store_float32x4(GibCursor *ref, __m128 v) {\n\
        \  _mm_storeu_ps((float *) (*ref), v);\n\
        \}\n\
        \\n\
        \#ifdef _WIN64\n\
        \#include <windows.h>\n\
        \#endif\n\n\
        \#ifdef _GIBBON_POINTER\n\
        \#include <gc.h>\n\
        \#endif\n\n\
        \#ifdef _GIBBON_PARALLEL\n\
        \#include <cilk/cilk.h>\n\
        \#include <cilk/cilk_api.h>\n\
        \#endif\n\n\
        \#ifdef _GIBBON_ENABLE_PAPI\n\
        \#include <papi.h>\n\
        \#endif\n\n\
        \#ifdef _GIBBON_ENABLE_PAPI_NATIVE\n\
        \static int gibbon_native_papi_eventset = PAPI_NULL;\n\
        \static int gibbon_native_papi_inited = 0;\n\
        \#define GIBBON_NATIVE_PAPI_EVENT_COUNT 7\n\
        \#define GIBBON_NATIVE_PAPI_MAX_ALTS 4\n\
        \static const char *gibbon_native_papi_metric_labels[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {\n\
        \    \"CPU_CYCLES\",\n\
        \    \"INSTRUCTIONS\",\n\
        \    \"L1D_LOAD_MISSES\",\n\
        \    \"L1I_LOAD_MISSES\",\n\
        \    \"L2D_MISSES\",\n\
        \    \"L2I_MISSES\",\n\
        \    \"LLC_LOAD_MISSES\",\n\
        \};\n\
        \static const char *gibbon_native_papi_event_candidates[GIBBON_NATIVE_PAPI_EVENT_COUNT][GIBBON_NATIVE_PAPI_MAX_ALTS] = {\n\
        \    {\"perf::PERF_COUNT_HW_CPU_CYCLES\", \"perf::CPU-CYCLES\", \"perf::CYCLES\", \"ix86arch::UNHALTED_CORE_CYCLES\"},\n\
        \    {\"perf::PERF_COUNT_HW_INSTRUCTIONS\", \"perf::INSTRUCTIONS\", \"ix86arch::INSTRUCTION_RETIRED\", NULL},\n\
        \    {\"perf::L1-DCACHE-LOAD-MISSES\", \"perf::PERF_COUNT_HW_CACHE_L1D\", NULL, NULL},\n\
        \    {\"perf::L1-ICACHE-LOAD-MISSES\", \"perf::PERF_COUNT_HW_CACHE_L1I\", NULL, NULL},\n\
        \    {\"L2_RQSTS:DEMAND_DATA_RD_MISS\", \"L2_RQSTS:MISS\", \"L2_REQUEST:DEMAND_DATA_RD_MISS\", \"L2_REQUEST:MISS\"},\n\
        \    {\"L2_RQSTS:CODE_RD_MISS\", \"L2_REQUEST:CODE_RD_MISS\", NULL, NULL},\n\
        \    {\"perf::LLC-LOAD-MISSES\", \"ix86arch::LLC_MISSES\", \"LONGEST_LAT_CACHE:MISS\", \"adl_grt::LONGEST_LAT_CACHE:MISS\"},\n\
        \};\n\
        \static const char *gibbon_native_papi_selected_events[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {NULL};\n\
        \static void papi_init_or_die(void) {\n\
        \    if (gibbon_native_papi_inited) return;\n\
        \    int rv = PAPI_library_init(PAPI_VER_CURRENT);\n\
        \    if (rv != PAPI_VER_CURRENT) {\n\
        \        fprintf(stderr, \"PAPI_library_init failed: %d\\n\", rv);\n\
        \        exit(1);\n\
        \    }\n\
        \    rv = PAPI_create_eventset(&gibbon_native_papi_eventset);\n\
        \    if (rv != PAPI_OK) {\n\
        \        fprintf(stderr, \"PAPI_create_eventset failed: %s\\n\", PAPI_strerror(rv));\n\
        \        exit(1);\n\
        \    }\n\
        \    for (int i = 0; i < GIBBON_NATIVE_PAPI_EVENT_COUNT; i++) {\n\
        \        int added = 0;\n\
        \        for (int j = 0; j < GIBBON_NATIVE_PAPI_MAX_ALTS; j++) {\n\
        \            const char *ev_name = gibbon_native_papi_event_candidates[i][j];\n\
        \            int code;\n\
        \            if (ev_name == NULL) {\n\
        \                continue;\n\
        \            }\n\
        \            rv = PAPI_event_name_to_code((char*)ev_name, &code);\n\
        \            if (rv != PAPI_OK) {\n\
        \                continue;\n\
        \            }\n\
        \            rv = PAPI_add_event(gibbon_native_papi_eventset, code);\n\
        \            if (rv == PAPI_OK) {\n\
        \                gibbon_native_papi_selected_events[i] = ev_name;\n\
        \                added = 1;\n\
        \                break;\n\
        \            }\n\
        \        }\n\
        \        if (!added) {\n\
        \            fprintf(stderr, \"No usable native PAPI event found for metric %s\\n\", gibbon_native_papi_metric_labels[i]);\n\
        \            exit(1);\n\
        \        }\n\
        \    }\n\
        \    gibbon_native_papi_inited = 1;\n\
        \}\n\
        \#endif\n\n\
        \/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\
        \ * Program starts here\n\
        \ * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\
        \ */\n\n"


builtinFieldTys :: [String]
builtinFieldTys =
    [ "GibInt", "GibFloat", "GibSym", "GibBool", "GibVector", "GibList", "GibCursor"
    -- , "GibPackedTag", "GibBoxedTag", "GibPtr", "GibSymDict", "GibSymSet"
    -- , "GibSymHash", "GibIntHash"
    ]

initSymTable :: SymTable -> C.Definition
initSymTable sym_tbl =
    let body =  map
          (\(k,v) -> case v of
                       -- Special symbols that get handled differently
                       "NEWLINE" -> C.BlockStm [cstm| gib_set_newline($k); |]
                       "COMMA" -> C.BlockStm [cstm| set_comma($k); |]
                       "SPACE" -> C.BlockStm [cstm| gib_set_space($k); |]
                       "LEFTPAREN" -> C.BlockStm [cstm| gib_set_leftparen($k); |]
                       "RIGHTPAREN" -> C.BlockStm [cstm| gib_set_rightparen($k); |]
                       -- Normal symbols just get added to the table
                       _ -> C.BlockStm [cstm| gib_add_symbol($k, $v); |]
          )
          (M.toList sym_tbl)
        fun = [cfun| void symbol_table_initialize(void) { $items:body } |]
    in C.FuncDef fun noLoc


initInfoTable :: InfoTable -> C.Definition
initInfoTable info_tbl =
    let info_table_len = length info_tbl + length builtinFieldTys
        body =  [ C.BlockDecl [cdecl| int error = gib_info_table_initialize($int:info_table_len); |]
                , C.BlockStm [cstm| if (error < 0) { fprintf(stderr, "Couldn't initialize info table, errorno=%d", error); exit(1); } |]
                ]  ++
                -- insert_scalar_info ++
                [ C.BlockDecl [cdecl| typename GibDatatype field_tys[$int:max_fields]; |] ] ++ insert_dcon_info ++
                [C.BlockStm [cstm| gib_info_table_finalize(); |] ]
        fun = [cfun| void info_table_initialize(void) { $items:body } |]
    in C.FuncDef fun noLoc
  where
    max_fields = M.foldr (\tyc_info acc ->
                              max acc $
                                  M.foldrWithKey (\dcon DataConInfo{num_scalars,num_packed} acc2 ->
                                                      if GL.isIndirectionTag dcon then acc2 else
                                                          (num_scalars + num_packed) `max` acc2)
                                                 0
                                                 tyc_info)
                         0
                         info_tbl
    _insert_scalar_info = map (\ty -> let ty_t = ty ++ "_T" in C.BlockStm [cstm| gib_info_table_insert_scalar($id:ty_t, sizeof($id:ty)); |]) builtinFieldTys

    insert_dcon_info = M.foldrWithKey
                           (\tycon tyc_info acc ->
                                M.foldrWithKey (\dcon (DataConInfo dcon_tag scalar_bytes num_shortcut num_scalars num_packed field_tys) acc2 ->
                                                    if GL.isIndirectionTag dcon then acc2 else
                                                    let packed_field_tys = filter GL.isPackedTy field_tys
                                                        set_field_tys =
                                                            map (\(ty,i) ->
                                                                     let ty' = (case ty of
                                                                                    GL.PackedTy tycon _ -> tycon
                                                                                    _ -> makeName' (fromL3Ty ty))
                                                                               ++ "_T"
                                                                         e = (C.Id ty' noLoc)
                                                                     in C.BlockStm [cstm| field_tys[$int:i] = ($id:e); |])
                                                                (zip packed_field_tys [0..])
                                                        tycon' = tycon ++ "_T"
                                                        insert_into_tbl = [ C.BlockStm [cstm| error = gib_info_table_insert_packed_dcon($id:tycon', $int:dcon_tag, $int:scalar_bytes, $int:num_shortcut, $int:num_scalars, $int:num_packed, field_tys, $int:num_packed); |]
                                                                          , C.BlockStm [cstm| if (error < 0) { fprintf(stderr, "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d", error, $id:tycon', $int:dcon_tag); exit(1); } |] ]
                                             in set_field_tys ++ insert_into_tbl ++ acc2)
                                        acc
                                        tyc_info)
                           []
                           info_tbl


makeStructs :: [[Ty]] -> [C.Definition]
makeStructs [] = []
makeStructs (ts : ts') =
      let strName = makeName ts
          decls = zipWith (\t n -> [csdecl| $ty:(codegenTy t) $id:("field"++(show n)); |]) ts [0 :: Int ..]
          d = [cedecl| typedef struct $id:(strName ++ "_struct") { $sdecls:decls } $id:strName; |]
      in d : makeStructs ts'

uniqueDicts :: [[Ty]] -> [[Ty]]
uniqueDicts [] = []
uniqueDicts (ts : ts') = (map f ts) : uniqueDicts ts'
    where f (SymDictTy _ t) = SymDictTy "_" t
          f t = t

-- | Replace returns with assignments to a given set of destinations.
rewriteReturns :: Tail -> [(Var,Ty)] -> Tail
rewriteReturns tl bnds =
 let go x = rewriteReturns x bnds in
 case tl of
   EndOfMain -> tl
   (RetValsT ls) -> AssnValsT [ (v,t,e) | (v,t) <- bnds | e <- ls ] Nothing
   (Goto _) -> tl

   -- Statement-like loop bodies can already be normalized to unit assignments.
   (AssnValsT upds mb_bod) -> AssnValsT upds (fmap go mb_bod)
   (e@LetCallT{bod})     -> e{bod = go bod }
   (e@LetPrimCallT{bod}) -> e{bod = go bod }
   (e@LetTrivT{bod})     -> e{bod = go bod }
   -- We don't recur on the "tails" under the if, because they're not
   -- tail with respect to our redex:
   (LetIfT bnd (a,b,c) bod) -> LetIfT bnd (a,b,c) (go bod)
   (LetTimedT flg bnd rhs bod) -> LetTimedT flg bnd rhs (go bod)
   (LetArenaT v bod) -> LetArenaT v (go bod)
   (LetUnpackT bs scrt body) -> LetUnpackT bs scrt (go body)
   (LetAllocT lhs vals body) -> LetAllocT lhs vals (go body)
   (LetAvailT vs body)       -> LetAvailT vs (go body)
   (ForLoopT idx bound loopBody body) -> ForLoopT idx bound loopBody (go body)
   (WhileCursorT ref loopBody body) -> WhileCursorT ref loopBody (go body)
   (WhileCursorEndT ref endRef loopBody body) -> WhileCursorEndT ref endRef loopBody (go body)
   (IfT a b c) -> IfT a (go b) (go c)
   (ErrT s) -> (ErrT s)
   (Switch lbl tr alts def) -> Switch lbl tr (mapAlts go alts) (fmap go def)
   -- Oops, this is not REALLY a tail call.  Hoist it and go under:
   (TailCall f rnds) -> let (vs,ts) = unzip bnds
                            vs' = map (toVar . (++"hack")) (map fromVar vs) -- FIXME: Gensym
                        in LetCallT False (zip vs' ts) f rnds
                            (rewriteReturns (RetValsT (map VarTriv vs')) bnds)
 where
   mapAlts f (TagAlts ls) = TagAlts $ zip (map fst ls) (map (f . snd) ls)
   mapAlts f (IntAlts ls) = IntAlts $ zip (map fst ls) (map (f . snd) ls)


-- dummyLoc :: SrcLoc
-- dummyLoc = (SrcLoc (Loc (Pos "" 0 0 0) (Pos "" 0 0 0)))

codegenTriv :: VEnv -> Triv -> C.Exp
codegenTriv _ (SizeOf ty) = [cexp| sizeof($ty:(codegenTy ty)) |]
codegenTriv _ (UninitTriv{}) = [cexp|  (void)0  |] -- noop
codegenTriv _ (VarTriv v) = C.Var (C.toIdent v noLoc) noLoc
codegenTriv _ (IntTriv i) = [cexp| $int:i |]
codegenTriv _ (CharTriv i) = [cexp| $char:i |]
codegenTriv _ (FloatTriv i) = [cexp| $double:i |]
codegenTriv _ (BoolTriv b) = case b of
                               True -> [cexp| true |]
                               False -> [cexp| false |]
codegenTriv _ (SymTriv i) = [cexp| $i |]
codegenTriv _ (TagTriv i) = if i == GL.indirectionAlt
                            then [cexp| GIB_INDIRECTION_TAG |]
                            else if i == GL.redirectionAlt
                            then [cexp| GIB_REDIRECTION_TAG |]
                            else if i == GL.selectiveIndirectionAlt
                            then [cexp| GIB_SELECTIVE_INDIRECTION_TAG |]
                            else [cexp| $i |]
codegenTriv venv (ProdTriv ls) =
  let ty = codegenTy $ typeOfTriv venv (ProdTriv ls)
      args = map (\a -> (Nothing,C.ExpInitializer (codegenTriv venv a) noLoc)) ls
  in [cexp| $(C.CompoundLit ty args noLoc) |]
codegenTriv venv (ProjTriv i trv) =
  let field = "field" ++ show i
  in [cexp| $(codegenTriv venv trv).$id:field |]
codegenTriv venv (IndexCursorArrayTriv idx v) = [cexp| $(codegenTriv venv v)[$int:idx] |]


-- Type environment
type FEnv = M.Map Var ([Ty], Ty)
type VEnv = M.Map Var Ty
type MutEndEnv = M.Map Var Var
type SyncDeps = [(Var, C.BlockItem)]

writeShadowstack :: Var
writeShadowstack = toVar "wstack"

readShadowstack :: Var
readShadowstack = toVar "rstack"

shadowstackFrame :: Var
shadowstackFrame = toVar "frame"

ssDecls :: [C.BlockItem]
ssDecls =
  [ C.BlockDecl [cdecl| $ty:stk_ty *$id:readShadowstack = DEFAULT_READ_SHADOWSTACK; |]
  , C.BlockDecl [cdecl| $ty:stk_ty *$id:writeShadowstack = DEFAULT_WRITE_SHADOWSTACK; |]
  , C.BlockDecl [cdecl| $ty:frame_ty *$id:shadowstackFrame; |]
  ]
  where
    stk_ty = [cty|typename GibShadowstack|]
    frame_ty = [cty|typename GibShadowstackFrame|]

-- | The central codegen function.
codegenTail :: VEnv -> MutEndEnv -> FEnv -> S.Set Var -> Tail -> Ty -> SyncDeps -> PassM [C.BlockItem]

codegenTail _ _ _ _ EndOfMain _ty _   = return []
-- Void type:
codegenTail _ _ _ _ (RetValsT []) _ty _   = return [ C.BlockStm [cstm| return 0; |] ]
-- Single return:
codegenTail venv _ _ _ (RetValsT [tr]) ty _ =
    case ty of
      ProdTy [_one] -> do
          let arg = [(Nothing,C.ExpInitializer (codegenTriv venv tr) noLoc)]
              ty' = codegenTy ty
          return $ [ C.BlockStm [cstm| return $(C.CompoundLit ty' arg noLoc); |] ]
      _ -> return [ C.BlockStm [cstm| return $(codegenTriv venv tr); |] ]
-- Multiple return:
codegenTail venv _ _ _ (RetValsT ts) ty _ = do 
    return_var <- gensym "return"
    let ty' = codegenTy ty
    let flds = foldl (\(vars, idx) _ -> 
                        let n = toVar ((fromVar return_var) ++ ".field"  ++ (show idx))
                         in (vars ++ [n], idx + 1) 
                     ) ([], 0) ts
    let init_ret = [ C.BlockDecl [cdecl| $ty:ty' $id:return_var; |]  ]
    let mem_copies = map (\(a, fld) -> let ty = typeOfTriv venv a
                                           a' = codegenTriv venv a
                                           ty' = codegenTy ty
                                         in case ty of 
                                              CursorArrayTy{} -> C.BlockStm  [cstm| memcpy($id:fld, $exp:a', sizeof($ty:ty')); |]
                                              --CursorTy -> C.BlockStm  [cstm| memcpy($id:fld, $exp:a', sizeof($ty:ty')); |] 
                                              --_ -> C.BlockStm  [cstm| memcpy(&$id:fld, &$exp:a', sizeof($ty:ty')); |]
                                              _ -> C.BlockStm [cstm| $id:fld = $exp:a'; |]
                         ) (zip ts (fst flds))
    return $ init_ret ++ mem_copies ++ [ C.BlockStm [cstm| return $id:return_var; |] ]

codegenTail venv mutEndEnv fenv sort_fns (AssnValsT ls bod_maybe) ty sync_deps = do
    case bod_maybe of
      Just bod -> do
        let venv' = (M.fromList $ map (\(a,b,_) -> (a,b)) ls)
                    `M.union` venv
        bod' <- codegenTail venv' mutEndEnv fenv sort_fns bod ty sync_deps
        return $ [ case ty of 
                       CursorArrayTy{} -> memcpy (codegenTy ty) vr (codegenTriv venv triv)
                       _ -> mut (codegenTy ty) vr (codegenTriv venv triv) 
                  | (vr,ty,triv) <- ls ] ++ bod'
      Nothing  ->
        return $ [ case ty of 
                        CursorArrayTy{} -> memcpy (codegenTy ty) vr (codegenTriv venv triv)
                        _ -> mut (codegenTy ty) vr (codegenTriv venv triv) 
                   | (vr,ty,triv) <- ls ]

codegenTail venv mutEndEnv fenv sort_fns (Switch lbl tr alts def) ty sync_deps =
    case def of
      Nothing  -> let (rest,lastone) = splitAlts alts in
                  genSwitch venv mutEndEnv fenv sort_fns lbl tr rest (altTail lastone) ty sync_deps
      Just def -> genSwitch venv mutEndEnv fenv sort_fns lbl tr alts def ty sync_deps

codegenTail venv _ _ _ (TailCall v ts) _ty _ =
    return $ [ C.BlockStm [cstm| return $( C.FnCall (cid v) (map (codegenTriv venv) ts) noLoc ); |] ]

codegenTail venv mutEndEnv fenv sort_fns (IfT e0 e1 e2) ty sync_deps = do
    e1' <- codegenTail venv mutEndEnv fenv sort_fns e1 ty sync_deps
    e2' <- codegenTail venv mutEndEnv fenv sort_fns e2 ty sync_deps
    return $ [ C.BlockStm [cstm| if ($(codegenTriv venv e0)) { $items:e1' } else { $items:e2' } |] ]

codegenTail _ _ _ _ (ErrT s) _ty _ = return $ [ C.BlockStm [cstm| printf("%s\n", $s); |]
                                              , C.BlockStm [cstm| exit(1); |] ]


-- We could eliminate these earlier
codegenTail venv mutEndEnv fenv sort_fns (LetTrivT (vr,rty,rhs) body) ty sync_deps =
    do let venv' = M.insert vr rty venv
           mutEndEnv' =
             case rhs of
               VarTriv src ->
                 case M.lookup src mutEndEnv of
                   Just endVar -> M.insert vr endVar mutEndEnv
                   Nothing -> M.delete vr mutEndEnv
               _ -> M.delete vr mutEndEnv
       tal <- codegenTail venv' mutEndEnv' fenv sort_fns body ty sync_deps
       {-Bad assumption?-}
       {-If it is a statically sized array -}
       -- if we have an array type that's being assigned 
       -- we can do a memcpy instead
       case rty of
          CursorArrayTy _size -> case rhs of 
                                    UninitTriv{} -> return $ [ C.BlockDecl [cdecl| $ty:(codegenTy rty) $id:vr; |] ] ++ tal
                                    _ -> return $ [ C.BlockDecl [cdecl| $ty:(codegenTy rty) $id:vr; |], 
                                                    C.BlockDecl [cdecl| $ty:(codegenTy rty) $id:vr = ($ty:(codegenTy rty)) $(codegenTriv venv rhs); |] ] ++ tal
          _ -> case rhs of 
                    UninitTriv{} -> return $ [ C.BlockDecl [cdecl| $ty:(codegenTy rty) $id:vr; |] ] ++ tal
                    _ -> return $ [ C.BlockDecl [cdecl| $ty:(codegenTy rty) $id:vr = ($ty:(codegenTy rty)) $(codegenTriv venv rhs); |] ]
                            ++ tal

-- TODO: extend rts with arena primitives, and invoke them here
codegenTail venv mutEndEnv fenv sort_fns (LetArenaT vr body) ty sync_deps =
    do tal <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps
       return $ [ C.BlockDecl [cdecl| $ty:(codegenTy ArenaTy) $id:vr = gib_alloc_arena();|] ]
              ++ tal

codegenTail venv mutEndEnv fenv sort_fns (LetAllocT lhs vals body) ty sync_deps =
    do let structTy = codegenTy (ProdTy (map fst vals))
           size = [cexp| sizeof($ty:structTy) |]
           venv' = M.insert lhs CursorTy venv
       tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
       dflags <- getDynFlags
       let alloc = if (gopt Opt_CountParRegions dflags) || (gopt Opt_CountAllRegions dflags)
                   then assn (codegenTy PtrTy) lhs [cexp| gib_alloc_counted_struct( $size ) |]
                   else assn (codegenTy PtrTy) lhs [cexp| gib_alloc( $size ) |]
       return$
              (alloc :
               [ C.BlockStm [cstm| (($ty:structTy *)  $id:lhs)->$id:fld = $(codegenTriv venv trv); |]
               | (ix,(_ty,trv)) <- zip [0 :: Int ..] vals
               , let fld = "field"++show ix] ++
                 tal)

codegenTail venv mutEndEnv fenv sort_fns (LetAvailT vs body) ty sync_deps =
    do let (avail, sync_deps') = L.partition (\(v,_) -> elem v vs) sync_deps
       tl <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps'
       pure $ (map snd avail) ++ tl

codegenTail venv mutEndEnv fenv sort_fns (ForLoopT idx bound loopBody body) ty sync_deps =
    do let venv' = M.insert idx IntTy venv
       loop' <- codegenTail venv' mutEndEnv fenv sort_fns loopBody (ProdTy []) sync_deps
       body' <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps
       let idx_ty = codegenTy IntTy
           bound' = codegenTriv venv bound
       pure $
         [ C.BlockStm [cstm| for ($ty:idx_ty $id:idx = 0; $id:idx < $exp:bound'; $id:idx++) { $items:loop' } |] ]
         ++ body'

codegenTail venv mutEndEnv fenv sort_fns (WhileCursorT ref loopBody body) ty sync_deps =
    do loop' <- codegenTail venv mutEndEnv fenv sort_fns loopBody (ProdTy []) sync_deps
       body' <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps
       pure $
         [ C.BlockStm [cstm| while (*$id:ref != NULL) { $items:loop' } |] ]
         ++ body'

codegenTail venv mutEndEnv fenv sort_fns (WhileCursorEndT ref endRef loopBody body) ty sync_deps =
    do loop' <- codegenTail venv mutEndEnv fenv sort_fns loopBody (ProdTy []) sync_deps
       body' <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps
       pure $
         [ C.BlockStm [cstm| while (*$id:ref != *$id:endRef) { $items:loop' } |] ]
         ++ body'

codegenTail venv mutEndEnv fenv sort_fns (LetUnpackT bs scrt body) ty sync_deps =
    do let mkFld :: Int -> C.Id
           mkFld i = C.toIdent ("field" ++ show i) noLoc

           fldTys = map snd bs
           struct_ty = codegenTy (ProdTy fldTys)

           mk_bind i (v, t) = [cdecl|
             $ty:(codegenTy t) $id:v = ( ( $ty:struct_ty * ) $exp:(cid scrt) )->$id:(mkFld i);
           |]

           binds = zipWith mk_bind [0..] bs
           venv' = (M.fromList bs) `M.union` venv

       body' <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
       return (map C.BlockDecl binds ++ body')

-- Here we unzip the tuple into assignments to local variables.
codegenTail venv mutEndEnv fenv sort_fns (LetIfT bnds (e0,e1,e2) body) ty sync_deps =

    do let decls = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:vr0; |]
                   | (vr0,ty0) <- bnds ]
       let e1' = rewriteReturns e1 bnds
           e2' = rewriteReturns e2 bnds

           venv' = (M.fromList bnds) `M.union` venv

       e1'' <- codegenTail venv' mutEndEnv fenv sort_fns e1' ty sync_deps
       e2'' <- codegenTail venv' mutEndEnv fenv sort_fns e2' ty sync_deps
       -- Int 1 is Boolean true:
       let ifbod = [ C.BlockStm [cstm| if ($(codegenTriv venv e0)) { $items:e1'' } else { $items:e2'' } |] ]
       tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
       return $ decls ++ ifbod ++ tal

codegenTail venv mutEndEnv fenv sort_fns (LetTimedT flg bnds rhs body) ty sync_deps =

    do let decls = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:vr0; |]
                   | (vr0,ty0) <- bnds ]
       let rhs' = rewriteReturns rhs bnds
       rhs'' <- codegenTail venv mutEndEnv fenv sort_fns rhs' ty sync_deps
       itertime  <- gensym "itertime"
       batchtime <- gensym "batchtime"
       selftimed <- gensym "selftimed"
       times <- gensym "times"
       tmp <- gensym "tmp"
       empty <- gensym "e" 
       papi_retval <- gensym "papi_retval"
       papi_region <- gensym "papi_region"
       papi_before <- gensym "papi_before"
       papi_after <- gensym "papi_after"
       papi_samples <- gensym "papi_samples"
       let timedResetVars = timedStateVars venv rhs
           timedEndResetVars = S.toList $ S.fromList $
             mapMaybe (\(v, vty) -> case vty of
                                      MutCursorTy -> M.lookup v mutEndEnv
                                      _ -> Nothing)
                     timedResetVars
       resetState <-
         fmap catMaybes $
           forM timedResetVars $ \(v, vty) ->
             case vty of
               MutCursorTy -> do
                 saved <- gensym $ toVar $ "saved_" ++ fromVar v
                 let decl = assn (codegenTy CursorTy) saved [cexp| *$id:v |]
                     restore = C.BlockStm [cstm| *$id:v = $id:saved; |]
                 pure $ Just ([decl], [restore])
               CursorArrayTy{} -> do
                 saved <- gensym $ toVar $ "saved_" ++ fromVar v
                 let decls' = initVarItems (codegenTy vty) saved (cid v)
                     restore = memcpy (codegenTy vty) v (cid saved)
                 pure $ Just (decls', [restore])
               _ ->
                 pure Nothing
       endResetState <-
         forM timedEndResetVars $ \endVar -> do
           saved <- gensym $ toVar $ "saved_" ++ fromVar endVar
           let decl = assn (codegenTy CursorTy) saved [cexp| *$id:endVar |]
               restore = C.BlockStm [cstm| *$id:endVar = $id:saved; |]
           pure ([decl], [restore])
       let ident = case bnds of
                     ((v,_):_) -> v
                     _ -> empty
           begn  = "begin_" ++ (fromVar ident)
           end   = "end_" ++ (fromVar ident)
           iters = "iters_"++ (fromVar ident)
           vec_ty = codegenTy (VectorTy FloatTy)
           resetDecls = concatMap fst (resetState ++ endResetState)
           resetBody = concatMap snd (resetState ++ endResetState)

           timebod = resetDecls ++
                     [ C.BlockDecl [cdecl| $ty:vec_ty ($id:times) = gib_vector_alloc(gib_get_iters_param(), sizeof(double)); |]
                     , C.BlockDecl [cdecl| struct timespec $id:begn; |]
                     , C.BlockDecl [cdecl| struct timespec $id:end; |] ] ++

                     (if flg
                         -- Save and restore EXCEPT on the last iteration.  This "cancels out" the effect of intermediate allocations.
                      then (let body = resetBody ++
                                       [ C.BlockStm [cstm| if ( $id:iters != gib_get_iters_param()-1) {
                                                         gib_list_bumpalloc_save_state();
                                                         gib_ptr_bumpalloc_save_state();
                                                         } |]
                                       , C.BlockStm [cstm| clock_gettime(CLOCK_MONOTONIC_RAW, & $id:begn );  |]
                                       ] ++
                                       rhs'' ++
                                       [ C.BlockStm [cstm| clock_gettime(CLOCK_MONOTONIC_RAW, &$(cid (toVar end))); |]
                                       , C.BlockStm [cstm| if ( $id:iters != gib_get_iters_param()-1) {
                                                         gib_list_bumpalloc_restore_state();
                                                         gib_ptr_bumpalloc_restore_state();
                                                         } |]
                                       , C.BlockDecl [cdecl| double $id:itertime = gib_difftimespecs(&$(cid (toVar begn)), &$(cid (toVar end))); |]
                                       , C.BlockStm [cstm| gib_vector_inplace_update($id:times, $id:iters, &($id:itertime)); |]
                                       ]
                                -- TODO: Find a better way to get a name for the region id.
                                ifdef_papi = "#ifdef _GIBBON_ENABLE_PAPI"
                                ifdef_papi_native = "#ifdef _GIBBON_ENABLE_PAPI_NATIVE"
                                ifndef_papi_native = "#ifndef _GIBBON_ENABLE_PAPI_NATIVE"
                                endif = "#endif"
                                body' = [   C.BlockStm [cstm| $escstm:ifdef_papi |]
                                          , C.BlockStm [cstm| $escstm:ifdef_papi_native |]
                                          , C.BlockStm [cstm| $id:papi_retval = PAPI_read(gibbon_native_papi_eventset, $id:papi_before);|]
                                          , C.BlockStm [cstm| if ( $id:papi_retval != PAPI_OK ) {
                                                                fprintf(stderr, "PAPI_read(before) failed: %s\n", PAPI_strerror($id:papi_retval));
                                                                exit(1);
                                                                } |]
                                          , C.BlockStm [cstm| $escstm:endif |]
                                          , C.BlockStm [cstm| $escstm:ifndef_papi_native |]
                                          , C.BlockDecl [cdecl| char $id:papi_region[128];|]
                                          , C.BlockStm [cstm| sprintf($id:papi_region, "%llu", (unsigned long long) get_papi_region_id());|]
                                          , C.BlockDecl [cdecl| int $id:papi_retval = PAPI_hl_region_begin($id:papi_region);|]
                                          , C.BlockStm [cstm| if ( $id:papi_retval != PAPI_OK ) {
                                                                exit(1);
                                                                } |]
                                          , C.BlockStm [cstm| $escstm:endif |]
                                          , C.BlockStm [cstm| $escstm:endif |]
                                        ] ++ 
                                        body ++ 
                                        [   C.BlockStm [cstm| $escstm:ifdef_papi |]
                                          , C.BlockStm [cstm| $escstm:ifdef_papi_native |]
                                          , C.BlockStm [cstm| $id:papi_retval = PAPI_read(gibbon_native_papi_eventset, $id:papi_after);|]
                                          , C.BlockStm [cstm| if ( $id:papi_retval != PAPI_OK ) {
                                                                fprintf(stderr, "PAPI_read(after) failed: %s\n", PAPI_strerror($id:papi_retval));
                                                                exit(1);
                                                                } |]
                                          , C.BlockStm [cstm| for (int papi_i = 0; papi_i < GIBBON_NATIVE_PAPI_EVENT_COUNT; papi_i++) {
                                                                $id:papi_samples[papi_i][$id:iters] = $id:papi_after[papi_i] - $id:papi_before[papi_i];
                                                              } |]
                                          , C.BlockStm [cstm| $escstm:endif |]
                                          , C.BlockStm [cstm| $escstm:ifndef_papi_native |]
                                          , C.BlockStm [cstm| $id:papi_retval = PAPI_hl_region_end($id:papi_region);|]
                                          , C.BlockStm [cstm| if ( $id:papi_retval != PAPI_OK ) {
                                                                exit(1);
                                                                } |]
                                          , C.BlockStm [cstm| increment_papi_region_id(); |]
                                          , C.BlockStm [cstm| $escstm:endif |]
                                          , C.BlockStm [cstm| $escstm:endif |]
                                        ]                                        
                            in [  C.BlockStm [cstm| $escstm:ifdef_papi |]
                                , C.BlockStm [cstm| $escstm:ifdef_papi_native |]
                                , C.BlockStm [cstm| papi_init_or_die(); |]
                                , C.BlockDecl [cdecl| int $id:papi_retval = PAPI_start(gibbon_native_papi_eventset);|]
                                , C.BlockStm [cstm| if ( $id:papi_retval != PAPI_OK ) {
                                                      fprintf(stderr, "PAPI_start failed: %s\n", PAPI_strerror($id:papi_retval));
                                                      exit(1);
                                                      } |]
                                , C.BlockDecl [cdecl| long long $id:papi_before[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {0};|]
                                , C.BlockDecl [cdecl| long long $id:papi_after[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {0};|]
                                , C.BlockDecl [cdecl| long long *$id:papi_samples[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {0};|]
                                , C.BlockStm [cstm| for (int papi_i = 0; papi_i < GIBBON_NATIVE_PAPI_EVENT_COUNT; papi_i++) {
                                                      $id:papi_samples[papi_i] = (long long*) malloc(sizeof(long long) * gib_get_iters_param());
                                                      if ($id:papi_samples[papi_i] == NULL) {
                                                          fprintf(stderr, "malloc failed for native PAPI samples\n");
                                                          exit(1);
                                                      }
                                                  } |]
                                , C.BlockStm [cstm| $escstm:endif |]
                                , C.BlockStm [cstm| $escstm:endif |]
                                , C.BlockStm [cstm| for (long long $id:iters = 0; $id:iters < gib_get_iters_param(); $id:iters ++) { $items:body' } |]
                                , C.BlockStm [cstm| $escstm:ifdef_papi |]
                                , C.BlockStm [cstm| $escstm:ifdef_papi_native |]
                                , C.BlockStm [cstm| $id:papi_retval = PAPI_stop(gibbon_native_papi_eventset, $id:papi_after);|]
                                , C.BlockStm [cstm| if ( $id:papi_retval != PAPI_OK ) {
                                                      fprintf(stderr, "PAPI_stop failed: %s\n", PAPI_strerror($id:papi_retval));
                                                      exit(1);
                                                      } |]
                                , C.BlockStm [cstm| for (long long iter_i = 0; iter_i < gib_get_iters_param(); iter_i++) {
                                                      for (int papi_i = 0; papi_i < GIBBON_NATIVE_PAPI_EVENT_COUNT; papi_i++) {
                                                          printf("PAPI_NATIVE %s[%s]=%lld\n",
                                                                 gibbon_native_papi_metric_labels[papi_i],
                                                                 gibbon_native_papi_selected_events[papi_i],
                                                                 $id:papi_samples[papi_i][iter_i]);
                                                      }
                                                  } |]
                                , C.BlockStm [cstm| for (int papi_i = 0; papi_i < GIBBON_NATIVE_PAPI_EVENT_COUNT; papi_i++) {
                                                      free($id:papi_samples[papi_i]);
                                                  } |]
                                , C.BlockStm [cstm| $escstm:endif |]
                                , C.BlockStm [cstm| $escstm:endif |]
                                , C.BlockStm [cstm| gib_vector_inplace_sort($id:times, gib_compare_doubles); |]
                                , C.BlockDecl [cdecl| double *$id:tmp = (double*) gib_vector_nth($id:times, (gib_get_iters_param() / 2)); |]
                                , C.BlockDecl [cdecl| double $id:selftimed = *($id:tmp); |]
                                , C.BlockDecl [cdecl| double $id:batchtime = gib_sum_timing_array($id:times); |]
                                , C.BlockStm [cstm| gib_print_timing_array($id:times); |]
                                , C.BlockStm [cstm| gib_vector_free($id:times); |]
                               ])

                         -- else
                      else [ C.BlockStm [cstm| clock_gettime(CLOCK_MONOTONIC_RAW, & $id:begn );  |]
                           , C.BlockStm [cstm| { $items:rhs'' } |]
                           , C.BlockStm [cstm| clock_gettime(CLOCK_MONOTONIC_RAW, &$(cid (toVar end))); |]
                           , C.BlockDecl [cdecl| double $id:selftimed = gib_difftimespecs(&$(cid (toVar begn)), &$(cid (toVar end))); |]
                           , C.BlockStm [cstm| gib_vector_free($id:times); |]
                           ])
           withPrnt = timebod ++
                      (if flg
                       then [ C.BlockStm [cstm| printf("ITERS: %ld\n", gib_get_iters_param()); |]
                            , C.BlockStm [cstm| printf("SIZE: %ld\n", gib_get_size_param()); |]
                            , C.BlockStm [cstm| printf("BATCHTIME: %e\n", $id:batchtime); |]
                            , C.BlockStm [cstm| printf("SELFTIMED: %e\n", $id:selftimed); |]
                            ]
                       else [ C.BlockStm [cstm| printf("SIZE: %ld\n", gib_get_size_param()); |]
                            , C.BlockStm [cstm| printf("SELFTIMED: %e\n", gib_difftimespecs(&$(cid (toVar begn)), &$(cid (toVar end)))); |] ])
       let venv' = (M.fromList bnds) `M.union` venv
       tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
       return $ decls ++ withPrnt ++ tal


codegenTail venv mutEndEnv fenv sort_fns (LetCallT False bnds ratr rnds body) ty sync_deps
    | [] <- bnds = do tal <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps
                      return $ [toStmt fnexp] ++ tal
    | [bnd] <- bnds =  let fn_ret_ty = snd (fenv M.! ratr)
                           venv' = (M.fromList bnds) `M.union` venv in
                       case fn_ret_ty of
                         -- Copied from the otherwise case below.
                         ProdTy [_one] -> do
                           nam <- gensym $ toVar "tmp_struct"
                           let bind (v,t) f = case t of 
                                                 CursorArrayTy{} -> initVarItems (codegenTy t) v (C.Member (cid nam) (C.toIdent f noLoc) noLoc)
                                                 _ -> [assn (codegenTy t) v (C.Member (cid nam) (C.toIdent f noLoc) noLoc)]
                               fields = map (\i -> "field" ++ show i) [0 :: Int .. length bnds - 1]
                               ty0 = ProdTy $ map snd bnds
                               init = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:nam = $(fnexp); |] ]
                           tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
                           return $ init ++ (concat $ zipWith bind bnds fields) ++ tal
                         ProdTy [] -> do
                           -- nam <- gensym "tmp"
                           let init = [ C.BlockDecl [cdecl| $ty:(codegenTy fn_ret_ty) $id:(fst bnd) = $(fnexp); |] ]
                           tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
                           return $ init ++ tal
                         _ -> do
                           tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
                           let call = assn (codegenTy (snd bnd)) (fst bnd) (fnexp)
                           return $ [call] ++ tal
    | otherwise = do
       nam <- gensym $ toVar "tmp_struct"
       let bind (v,t) f = case t of 
                            CursorArrayTy{} -> initVarItems (codegenTy t) v (C.Member (cid nam) (C.toIdent f noLoc) noLoc)
                            _ -> [assn (codegenTy t) v (C.Member (cid nam) (C.toIdent f noLoc) noLoc)]
           fields = map (\i -> "field" ++ show i) [0 :: Int .. length bnds - 1]
           ty0 = ProdTy $ map snd bnds
           init = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:nam = $(fnexp); |] ]
           venv' = (M.fromList bnds) `M.union` venv
       tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
       return $ init ++ (concat $ zipWith bind bnds fields) ++ tal
  where
    fncall =
      let rnds' = map (codegenTriv venv) rnds
          rnds'' = if S.member ratr sort_fns
                   then map (\rnd -> [cexp| &$rnd|]) rnds'
                   else rnds'
      in C.FnCall (cid ratr) rnds'' noLoc
    fnexp = C.EscExp (prettyCompact (space <> ppr fncall)) noLoc

codegenTail venv mutEndEnv fenv sort_fns (LetCallT True bnds ratr rnds body) ty sync_deps
    | [] <- bnds = do tal <- codegenTail venv mutEndEnv fenv sort_fns body ty sync_deps
                      return $ [toStmt spawnexp] ++ tal
    | [bnd] <- bnds  = let fn_ret_ty = snd (fenv M.! ratr)
                           venv' = (M.fromList bnds) `M.union` venv in
                       case fn_ret_ty of
                         -- Copied from the otherwise case below.
                         ProdTy [_one] -> do
                           nam <- gensym $ toVar "tmp_struct"
                           let bind (v,t) f = (v, assn (codegenTy t) v (C.Member (cid nam) (C.toIdent f noLoc) noLoc))
                               fields = map (\i -> "field" ++ show i) [0 :: Int .. length bnds - 1]
                               ty0 = ProdTy $ map snd bnds
                               init = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:nam = $(spawnexp); |] ]
                               bind_after_sync = zipWith bind bnds fields
                           tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty (sync_deps ++ bind_after_sync)
                           return $ init ++ tal
                         ProdTy _ -> error $ "codegenTail: LetCallT" ++ fromVar ratr
                         _ -> do
                           tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty sync_deps
                           let call = assn (codegenTy (snd bnd)) (fst bnd) (spawnexp)
                           return $ [call] ++ tal
    | otherwise = do
       nam <- gensym $ toVar "tmp_struct"
       let bind (v,t) f = (v, assn (codegenTy t) v (C.Member (cid nam) (C.toIdent f noLoc) noLoc))
           fields = map (\i -> "field" ++ show i) [0 :: Int .. length bnds - 1]
           ty0 = ProdTy $ map snd bnds
           init = [ C.BlockDecl [cdecl| $ty:(codegenTy ty0) $id:nam = $(spawnexp); |] ]

       let bind_after_sync = zipWith bind bnds fields
           venv' = (M.fromList bnds) `M.union` venv
       tal <- codegenTail venv' mutEndEnv fenv sort_fns body ty (sync_deps ++ bind_after_sync)
       return $ init ++  tal
  where
    fncall = C.FnCall (cid ratr) (map (codegenTriv venv) rnds) noLoc
    spawnexp = C.EscExp (prettyCompact (text "cilk_spawn" <> space <> ppr fncall)) noLoc
    _seqexp = C.EscExp (prettyCompact (ppr fncall)) noLoc

codegenTail venv mutEndEnv fenv sort_fns (LetPrimCallT bnds prm rnds body) ty sync_deps =
    do let venv'base = (M.fromList bnds) `M.union` venv
           (venv', mutEndEnv') =
             case prm of
               NewBuffer _ endregmod
                 | endregmod == L2.RegionMutable ->
                     case bnds of
                       [(_, CursorTy), (outV, CursorTy), (_, CursorTy)] ->
                         ( M.insert (toEndV outV) MutCursorTy venv'base
                         , M.insert outV (toEndV outV) mutEndEnv
                         )
                       _ ->
                         (venv'base, mutEndEnv)
               AddrOfCursor ->
                 case (bnds, rnds) of
                   ([(outV, MutCursorTy)], [VarTriv src]) ->
                     case M.lookup src mutEndEnv of
                       Just endVar -> (venv'base, M.insert outV endVar mutEndEnv)
                       Nothing -> (venv'base, mutEndEnv)
                   _ ->
                     (venv'base, mutEndEnv)
               BoundsCheck L2.OutputMutable ->
                 case rnds of
                   [_, VarTriv bound, VarTriv cur, _, _] ->
                     (venv'base, M.insert cur bound mutEndEnv)
                   _ ->
                     (venv'base, mutEndEnv)
               BoundsCheckVector ->
                 let addBoundForCur acc triv =
                       case triv of
                         ProdTriv [_, VarTriv bound, VarTriv cur, _] ->
                           M.insert cur bound acc
                         _ -> acc
                  in (venv'base, foldl addBoundForCur mutEndEnv rnds)
               _ ->
                 (venv'base, mutEndEnv)
       bod' <- case prm of
                 ParSync -> codegenTail venv' mutEndEnv' fenv sort_fns body ty []
                 _       -> codegenTail venv' mutEndEnv' fenv sort_fns body ty sync_deps
       dflags <- getDynFlags
       let isPacked = gopt Opt_Packed dflags
           noGC = gopt Opt_DisableGC dflags
           genGC = gopt Opt_GenGc dflags

       pre <- case prm of
                 AddP -> let [(outV,outT)] = bnds
                             [pleft,pright] = rnds in pure
                         [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $(codegenTriv venv pleft) + $(codegenTriv venv pright); |] ]
                 BumpCursorMutable -> let [(_outV,_outT)] = bnds
                                          [pleft,pright] = rnds in pure
                                      [C.BlockStm [cstm| *($(codegenTriv venv pleft)) += $(codegenTriv venv pright); |]] 
                 SubP -> let (outV,outT) = Sf.headErr bnds
                             [pleft,pright] = rnds
                             ptrExp trv =
                               case trv of
                                 VarTriv v | M.lookup v venv == Just MutCursorTy ->
                                   [cexp| *$id:v |]
                                 _ ->
                                   codegenTriv venv trv
                         in pure
                              [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $exp:(ptrExp pleft) - $exp:(ptrExp pright); |] ]
                 MulP -> let [(outV,outT)] = bnds
                             [pleft,pright] = rnds in pure
                         [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $(codegenTriv venv pleft) * $(codegenTriv venv pright); |]]
                 DivP -> let [(outV,outT)] = bnds
                             [pleft,pright] = rnds in pure
                         [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $(codegenTriv venv pleft) / $(codegenTriv venv pright); |]]
                 ModP -> let [(outV,outT)] = bnds
                             [pleft,pright] = rnds in pure
                         [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $(codegenTriv venv pleft) % $(codegenTriv venv pright); |]]
                 ExpP -> let [(outV,outT)] = bnds
                             [pleft,pright] = rnds in pure
                         [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_expll($(codegenTriv venv pleft), $(codegenTriv venv pright)); |]]
                 RandP -> let [(outV,outT)] = bnds in pure
                          [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = rand(); |]]
                 FRandP-> let [(outV,outT)] = bnds
                              fty = codegenTy FloatTy in pure
                          [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($ty:fty) rand() / ($ty:fty) (RAND_MAX); |]]
                 FSqrtP -> let [(outV,outT)] = bnds
                               [arg] = rnds in pure
                           [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = sqrt($(codegenTriv venv arg)) ; |]]

                 FTanP -> let [(outV,outT)] = bnds
                              [arg] = rnds in pure
                           [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = tan($(codegenTriv venv arg)) ; |]]

                 FloatToIntP -> let [(outV,outT)] = bnds
                                    [arg] = rnds
                                    ity= codegenTy IntTy in pure
                                [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($ty:ity) ($(codegenTriv venv arg)) ; |]]

                 IntToFloatP -> let [(outV,outT)] = bnds
                                    [arg] = rnds
                                    fty = codegenTy FloatTy in pure
                                [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($ty:fty) ($(codegenTriv venv arg)) ; |]]

                 EqP -> let [(outV,outT)] = bnds
                            [pleft,pright] = rnds in pure
                        [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) == $(codegenTriv venv pright)); |]]
                 LtP -> let [(outV,outT)] = bnds
                            [pleft,pright] = rnds in pure
                        [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) < $(codegenTriv venv pright)); |]]
                 GtP -> let [(outV,outT)] = bnds
                            [pleft,pright] = rnds in pure
                        [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) > $(codegenTriv venv pright)); |]]
                 LtEqP -> let [(outV,outT)] = bnds
                              [pleft,pright] = rnds in pure
                          [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) <= $(codegenTriv venv pright)); |]]
                 GtEqP -> let [(outV,outT)] = bnds
                              [pleft,pright] = rnds in pure
                          [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) >= $(codegenTriv venv pright)); |]]
                 OrP -> let [(outV,outT)] = bnds
                            [pleft,pright] = rnds in pure
                        [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) || $(codegenTriv venv pright)); |]]
                 AndP -> let [(outV,outT)] = bnds
                             [pleft,pright] = rnds in pure
                        [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($(codegenTriv venv pleft) && $(codegenTriv venv pright)); |]]

                 EqSymP -> let [(outV,outT)] = bnds
                               [pleft,pright] = rnds in pure
                           [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $(codegenTriv venv pleft) == $(codegenTriv venv pright); |]]

                 EqBenchProgP str -> let [(outV,outT)] = bnds
                                     in pure [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = strcmp($str,gib_read_bench_prog_param()) == 0; |]]

                 DictInsertP _ -> let [(outV,ty)] = bnds
                                      [(VarTriv arena),(VarTriv dict),keyTriv,valTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_dict_insert_ptr($id:arena, $id:dict, $(codegenTriv venv keyTriv), $(codegenTriv venv valTriv)); |] ]
                 DictLookupP _ -> let [(outV,ty)] = bnds
                                      [(VarTriv dict),keyTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_dict_lookup_ptr($id:dict, $(codegenTriv venv keyTriv)); |] ]
                 DictEmptyP _ty -> let [(outV,ty)] = bnds
                                   in pure [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = 0; |] ]
                 -- DictHasKeyP PtrTy -> let [(outV,IntTy)] = bnds
                 --                          [(VarTriv dict)] = rnds in pure
                 --    [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:outV = dict_has_key_ptr($id:dict); |] ]
                 DictHasKeyP _ -> error $ "codegen: " ++ show prm ++ " unhandled."

                 SymSetEmpty -> let [(outV,outT)] = bnds
                                in pure [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_empty_set(); |] ]
                 SymSetInsert -> let [(outV,outT)] = bnds
                                     [(VarTriv set),valTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_insert_set($id:set, $(codegenTriv venv valTriv)); |] ]
                 SymSetContains -> let [(outV,ty)] = bnds
                                       [(VarTriv set),valTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_contains_set($id:set, $(codegenTriv venv valTriv)); |] ]

                 SymHashEmpty -> let [(outV,outT)] = bnds
                                 in pure [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_empty_hash(); |] ]
                 SymHashInsert -> let [(outV,outT)] = bnds
                                      [(VarTriv hash),keyTriv,valTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_insert_hash($id:hash, $(codegenTriv venv keyTriv), $(codegenTriv venv valTriv)); |] ]
                 SymHashLookup -> let [(outV,ty)] = bnds
                                      [(VarTriv hash),keyTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_lookup_hash($id:hash, $(codegenTriv venv keyTriv)); |] ]

                 SymHashContains -> let [(outV,ty)] = bnds
                                        [(VarTriv hash),keyTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_contains_hash($id:hash, $(codegenTriv venv keyTriv)); |] ]

                 IntHashEmpty -> let [(outV,outT)] = bnds
                                 in pure [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_empty_hash(); |] ]
                 IntHashInsert -> let [(outV,outT)] = bnds
                                      [(VarTriv hash),keyTriv,valTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = gib_insert_hash($id:hash, $(codegenTriv venv keyTriv), $(codegenTriv venv valTriv)); |] ]
                 IntHashLookup -> let [(outV,ty)] = bnds
                                      [(VarTriv hash),keyTriv] = rnds in pure
                    [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_lookup_hash($id:hash, $(codegenTriv venv keyTriv)); |] ]
                 NewBuffer mul endregmod -> do
                   dflags <- getDynFlags
                   let countRegions = gopt Opt_CountAllRegions dflags
                   let [(reg, CursorTy),(outV,CursorTy), (endV, CursorTy)] = bnds
                       bufsize = codegenMultiplicity mul
                   let additional_bnds = if endregmod == L2.RegionMutable
                                         then [C.BlockDecl [cdecl| $ty:(codegenTy MutCursorTy) $id:(toEndV outV) = &($id:endV); |]]
                                         else []
                   if countRegions
                   then
                     pure $
                       [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy)* $id:reg = gib_alloc_counted_region($exp:bufsize); |]
                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = $id:reg->start; |]
                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:endV = $id:reg->end; |]
                       ] ++ additional_bnds
                   else
                     pure $
                       (if genGC
                        then [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy) $id:reg = gib_alloc_region($exp:bufsize); |] ]
                        else [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy) $id:reg = gib_alloc_region_on_heap($exp:bufsize); |] ]) ++
                          [ C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = $id:reg.start; |]
                          , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:endV = $id:reg.end; |]
                          ] ++ additional_bnds


                 NewParBuffer mul -> do
                   dflags <- getDynFlags
                   let countRegions = gopt Opt_CountParRegions dflags
                   let [(reg, CursorTy),(outV,CursorTy),(endV,CursorTy)] = bnds
                       bufsize = codegenMultiplicity mul
                   if countRegions
                   then
                     pure
                       [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy)* $id:reg = gib_alloc_counted_region($exp:bufsize); |]
                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = $id:reg->start; |]
                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:endV = $id:reg->end; |]
                       ]
                   else
                     pure $
                       (if genGC
                        then [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy) $id:reg = gib_alloc_region($exp:bufsize); |] ]
                        else [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy) $id:reg = gib_alloc_region_on_heap($exp:bufsize); |] ]) ++
                          [ C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = $id:reg.start; |]
                          , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:endV = $id:reg.end; |]
                          ]
                 ScopedBuffer mul -> let [(outV,CursorTy)] = bnds
                                         bufsize = codegenMultiplicity mul
                                     in pure
                             [ C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ( $ty:(codegenTy CursorTy) ) gib_scoped_alloc($exp:bufsize); |] ]

                 ScopedParBuffer mul -> let [(outV,CursorTy)] = bnds
                                            bufsize = codegenMultiplicity mul
                                        in pure
                             [ C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ( $ty:(codegenTy CursorTy) ) gib_scoped_alloc($exp:bufsize); |] ]

                 -- generated during newbuffer.
                 EndOfBuffer{} -> pure []

                 FreeBuffer -> if noGC || genGC
                               then pure []
                               else
                                 let [(VarTriv _reg),(VarTriv _rcur),(VarTriv endr_cur)] = rnds
                                 in case M.lookup endr_cur mutEndEnv of
                                      Just{} ->
                                        pure [ C.BlockStm [cstm| gib_free_region(*$id:endr_cur); |] ]
                                      Nothing ->
                                        case M.lookup endr_cur venv of
                                          Just MutCursorTy ->
                                            pure [ C.BlockStm [cstm| gib_free_region(*$id:endr_cur); |] ]
                                          _ ->
                                            pure [ C.BlockStm [cstm| gib_free_region($id:endr_cur); |] ]

                 WriteTag -> let [(outV,CursorTy)] = bnds
                                 [t@(TagTriv{}),(VarTriv cur)] = rnds in pure
                             [ C.BlockStm [cstm| *($ty:(codegenTy TagTyPacked) *) ($id:cur) = $(codegenTriv venv t); |]
                             , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = $id:cur + 1; |] ]
                 WriteTagPacked -> let [(outV,CursorTy)] = bnds
                                       [tagv,(VarTriv cur)] = rnds in pure
                                   [ C.BlockStm [cstm| *($ty:(codegenTy TagTyPacked) *) ($id:cur) = $(codegenTriv venv tagv); |]
                                   , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = $id:cur + 1; |] ]
                 ReadTag -> let [(tagV,TagTyPacked),(curV,CursorTy)] = bnds
                                [(VarTriv cur)] = rnds in pure
                            [ C.BlockDecl [cdecl| $ty:(codegenTy TagTyPacked) $id:tagV = *($ty:(codegenTy TagTyPacked) *) ($id:cur); |]
                            , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:curV = $id:cur + 1; |] ]

                 WriteScalar s -> let [(outV,CursorTy)] = bnds
                                      [val,(VarTriv cur)] = rnds in pure
                                  [ C.BlockStm [cstm| *( $ty:(codegenTy (scalarToTy s))  *)($id:cur) = $(codegenTriv venv val); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($id:cur) + sizeof( $ty:(codegenTy (scalarToTy s)) ); |] ]

                 ScalarCountFooterBegin -> do
                   when (not (null bnds) || not (null rnds)) $
                     error $ "ScalarCountFooterBegin expected no bindings/args: " ++ show (bnds, rnds)
                   pure [ C.BlockStm [cstm| gib_scalar_count_footer_begin(); |] ]

                 ScalarCountBump -> do
                   when (not (null bnds)) $
                     error $ "ScalarCountBump expected no bindings: " ++ show (bnds, rnds)
                   let footer_arg footer =
                         case footer of
                           VarTriv v ->
                             case M.lookup v mutEndEnv of
                               Just endVar -> [cexp| $id:endVar |]
                               Nothing -> codegenTriv venv footer
                           _ -> codegenTriv venv footer
                   pure $
                     L.map
                       (\footer ->
                           let footer_arg' = footer_arg footer
                           in C.BlockStm [cstm| gib_scalar_count_footer_bump($exp:footer_arg'); |])
                       rnds

                 ScalarCountSet -> do
                   when (not (null bnds) || length rnds /= 2) $
                     error $ "ScalarCountSet expected no bindings and two args: " ++ show (bnds, rnds)
                   let [footer, count] = rnds
                       footer_arg =
                         case footer of
                           VarTriv v ->
                             case M.lookup v mutEndEnv of
                               Just endVar -> [cexp| $id:endVar |]
                               Nothing -> codegenTriv venv footer
                           _ -> codegenTriv venv footer
                   pure [ C.BlockStm [cstm| gib_scalar_count_footer_set($exp:footer_arg, $(codegenTriv venv count)); |] ]

                 ScalarCountCopyAll len -> do
                   when (not (null bnds) || length rnds /= 2) $
                     error $ "ScalarCountCopyAll expected no bindings and two args: " ++ show (bnds, rnds)
                   let [(VarTriv dstEnds), (VarTriv srcEnds)] = rnds
                   pure [ C.BlockStm [cstm| gib_scalar_count_copy_all($id:dstEnds, $id:srcEnds, $int:len); |] ]

                 ScalarCountFooterEnd fun_name -> do
                   when (not (null bnds) || not (null rnds)) $
                     error $ "ScalarCountFooterEnd expected no bindings/args: " ++ show (bnds, rnds)
                   pure [ C.BlockStm [cstm| gib_scalar_count_footer_end($string:fun_name); |] ]

                 ScalarCountGet -> do
                   let [(outV, outTy)] = bnds
                       [footer] = rnds
                   pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = gib_scalar_count_footer_get($(codegenTriv venv footer)); |] ]

                 ScalarCountFirstFooter -> do
                   let [(outV, outTy)] = bnds
                       [footer] = rnds
                   pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = gib_scalar_count_first_footer($(codegenTriv venv footer)); |] ]

                 ScalarCountNextFooter -> do
                   let [(outV, outTy)] = bnds
                       [footer] = rnds
                   pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = gib_scalar_count_footer_next($(codegenTriv venv footer)); |] ]

                 VecBroadcast s lanes ->
                   codegenVecBroadcast venv bnds s lanes rnds

                 VecLoad s lanes ->
                   codegenVecLoad venv bnds s lanes rnds

                 VecAdd s lanes ->
                   codegenVecAdd venv bnds s lanes rnds

                 VecSub s lanes ->
                   codegenVecSub venv bnds s lanes rnds

                 VecMul s lanes ->
                   codegenVecMul venv bnds s lanes rnds

                 VecDiv s lanes ->
                   codegenVecDiv venv bnds s lanes rnds

                 VecMod s lanes ->
                   codegenVecMod venv bnds s lanes rnds

                 VecEq s lanes ->
                   codegenVecEq venv bnds s lanes rnds

                 VecSelect s lanes ->
                   codegenVecSelect venv bnds s lanes rnds

                 VecStore s lanes ->
                   codegenVecStore venv bnds s lanes rnds

                 ReadScalar s -> let [(valV,valTy),(curV,CursorTy)] = bnds
                                     [(VarTriv cur)] = rnds in pure
                                     [ C.BlockDecl [cdecl| $ty:(codegenTy valTy) $id:valV = *( $ty:(codegenTy valTy) *)($id:cur); |]
                                     , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:curV = ($id:cur) + sizeof( $ty:(codegenTy (scalarToTy s))); |] ]

                 TagCursor  -> let [(taggedV,_)] = bnds
                                   [(VarTriv a), (VarTriv b)] = rnds
                                   tag_t = [cty| typename uint16_t |]
                                   tagged_ptr_t = [cty| typename uintptr_t |]
                               in do offset <- gensym "offset"
                                     pure
                                       [ C.BlockDecl [cdecl| $ty:tag_t $id:offset = $id:b - $id:a; |]
                                       , C.BlockDecl [cdecl| $ty:tagged_ptr_t $id:taggedV = GIB_STORE_TAG($id:a, $id:offset); |]
                                       ]

                 WriteCursorIndirection ->
                               let [(outV,CursorTy)] = bnds
                                   [(VarTriv cur), (VarTriv to), (VarTriv toEnd)] = rnds
                                   cursorLikeExp v =
                                     case M.lookup v venv of
                                       Just MutCursorTy ->
                                         [cexp| *$id:v |]
                                       _ ->
                                         [cexp| $id:v |]
                                   cur' = cursorLikeExp cur
                                   to' = cursorLikeExp to
                                   toEnd' = cursorLikeExp toEnd
                                   tag_t = [cty| typename uint16_t |]
                                   tagged_ptr_t = [cty| typename uintptr_t |]
                               in do offset <- gensym "offset"
                                     tagged <- gensym "tagged"
                                     writeloc <- gensym "writeloc"
                                     pure
                                       [ C.BlockDecl [cdecl| $ty:tag_t $id:offset = $exp:toEnd' - $exp:to'; |]
                                       , C.BlockDecl [cdecl| $ty:tagged_ptr_t $id:tagged = GIB_STORE_TAG($exp:to', $id:offset); |]
                                       , assn [cty| char * |] writeloc [cexp| (char *) $exp:cur' |]
                                       , C.BlockStm [cstm| *$id:writeloc = GIB_INDIRECTION_TAG; |]
                                       , C.BlockStm [cstm| gib_store_taggedptr_unaligned($exp:cur' + sizeof(GibPackedTag), $id:tagged); |]
                                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($exp:cur') + 9; |]
                                       ]

                 WriteCursorSelectiveIndirection ->
                               let [(outV,CursorTy)] = bnds
                                   [(VarTriv cur), (VarTriv to), (VarTriv toEnd), mask] = rnds
                                   cursorLikeExp v =
                                     case M.lookup v venv of
                                       Just MutCursorTy ->
                                         [cexp| *$id:v |]
                                       _ ->
                                         [cexp| $id:v |]
                                   cur' = cursorLikeExp cur
                                   to' = cursorLikeExp to
                                   toEnd' = cursorLikeExp toEnd
                                   mask' = codegenTriv venv mask
                                   tagged_ptr_t = [cty| typename uintptr_t |]
                                   mask_t = [cty| typename uint64_t |]
                               in do writeloc <- gensym "writeloc"
                                     pure
                                       [ assn [cty| char * |] writeloc [cexp| (char *) $exp:cur' |]
                                       , C.BlockStm [cstm| *$id:writeloc = GIB_SELECTIVE_INDIRECTION_TAG; |]
                                       , C.BlockStm [cstm| *($ty:tagged_ptr_t *)($exp:cur' + sizeof(GibPackedTag)) = ($ty:tagged_ptr_t) $exp:to'; |]
                                       , C.BlockStm [cstm| *($ty:tagged_ptr_t *)($exp:cur' + sizeof(GibPackedTag) + sizeof(uintptr_t)) = ($ty:tagged_ptr_t) $exp:toEnd'; |]
                                       , C.BlockStm [cstm| *($ty:mask_t *)($exp:cur' + sizeof(GibPackedTag) + (2 * sizeof(uintptr_t))) = ($ty:mask_t) $exp:mask'; |]
                                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($exp:cur') + 25; |]
                                       ]

                 UnwrapSelectiveIndirections len ->
                               let [(VarTriv ends), (VarTriv curs)] = rnds
                               in pure
                                  [ C.BlockStm [cstm| gib_unwrap_selective_indirections($id:ends, $id:curs, $int:len); |] ]

                 ReadTaggedCursor -> do
                               tagged <- gensym "tagged_tmpcur"
                               let [(next,CursorTy),(afternext,CursorTy),(tag,IntTy)] = bnds
                                   [(VarTriv cur)] = rnds
                                   tagged_t = [cty| typename uintptr_t |]
                                   tag_t = [cty| typename uint16_t |]
                               pure
                                 [ C.BlockDecl [cdecl| $ty:tagged_t $id:tagged = *($ty:tagged_t *) ($id:cur); |]
                                 , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:next = GIB_UNTAG($id:tagged); |]
                                 , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:afternext = ($id:cur) + 8; |]
                                 , C.BlockDecl [cdecl| $ty:tag_t $id:tag = GIB_GET_TAG($id:tagged); |]
                                 ]

                 WriteTaggedCursor ->
                                let [(outV,CursorTy)] = bnds
                                    [val,(VarTriv cur)] = rnds
                                    tagged_t = [cty| typename uintptr_t |] in pure
                                 [ C.BlockStm [cstm| *( $ty:tagged_t  *)($id:cur) = ($ty:tagged_t) $(codegenTriv venv val); |]
                                 , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($id:cur) + 8; |] ]

                 MemCpy -> let [(VarTriv copy_to), (VarTriv copy_from), size] = rnds in pure
                             [ C.BlockStm [cstm| memcpy($id:copy_to, $id:copy_from, $(codegenTriv venv size)); |] ]

                --  MemCpy -> let [(UninitTriv copy_to _ _), (VarTriv copy_from), size] = rnds in pure
                --              [ C.BlockStm [cstm| memcpy($id:copy_to, $id:copy_from, $(codegenTriv venv size)); |] ]

                 ReadCursor -> let [(next,CursorTy),(afternext,CursorTy)] = bnds
                                   [(VarTriv cur)] = rnds in pure
                               [ C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:next = *($ty:(codegenTy CursorTy) *) ($id:cur); |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:afternext = ($id:cur) + 8; |]
                               ]

                 GrowRegion -> let [(_outV,ProdTy [])] = bnds
                                   [(VarTriv cur), (VarTriv end)] = rnds in pure
                               [ C.BlockStm [cstm| gib_grow_region($id:cur, $id:end); |] ]

                 WriteCursorMutable -> let [(_outV,CursorTy)] = bnds
                                           [val,(VarTriv cur)] = rnds in pure
                                       -- , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($id:cur) + 8; |]
                                       [ C.BlockStm [cstm| *( $ty:(codegenTy CursorTy)  *)($id:cur) = $(codegenTriv venv val); |]]

                 WriteList    -> let [(outV,CursorTy)] = bnds
                                     [val,(VarTriv cur)] = rnds
                                     ls_ty = ListTy (ProdTy []) in pure
                                  [ C.BlockStm [cstm| *( $ty:(codegenTy ls_ty)  *)($id:cur) = $(codegenTriv venv val); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($id:cur) + sizeof( $ty:(codegenTy ls_ty) ); |] ]

                 ReadList     -> let [(valV,valTy),(curV,CursorTy)] = bnds
                                     [(VarTriv cur)] = rnds in pure
                                     [ C.BlockDecl [cdecl| $ty:(codegenTy valTy) $id:valV = *( $ty:(codegenTy valTy) *)($id:cur); |]
                                     , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:curV = ($id:cur) + sizeof( $ty:(codegenTy valTy)); |] ]


                 WriteVector    -> let [(outV,CursorTy)] = bnds
                                       [val,(VarTriv cur)] = rnds
                                       ls_ty = VectorTy (ProdTy []) in pure
                                  [ C.BlockStm [cstm| *( $ty:(codegenTy ls_ty)  *)($id:cur) = $(codegenTriv venv val); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ($id:cur) + sizeof( $ty:(codegenTy ls_ty) ); |] ]

                 ReadVector     -> let [(valV,valTy),(curV,CursorTy)] = bnds
                                       [(VarTriv cur)] = rnds in pure
                                       [ C.BlockDecl [cdecl| $ty:(codegenTy valTy) $id:valV = *( $ty:(codegenTy valTy) *)($id:cur); |]
                                       , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:curV = ($id:cur) + sizeof( $ty:(codegenTy valTy)); |] ]

                 IndirectionBarrier tycon ->
                   let [(VarTriv from_loc), (VarTriv end_from_reg),
                        (VarTriv to_loc), (VarTriv end_to_reg)] = rnds
                       tycon_t = (C.Id (tycon ++ "_T") noLoc)
                   in pure [ C.BlockStm [cstm| gib_indirection_barrier($id:from_loc, $id:end_from_reg, $id:to_loc, $id:end_to_reg, $id:tycon_t); |] ]

                 BoundsCheck mode -> do
                   _new_chunk   <- gensym "new_chunk"
                   _chunk_start <- gensym "chunk_start"
                   _chunk_end   <- gensym "chunk_end"
                   case mode of 
                     L2.Output -> do
                        let [(IntTriv i),(VarTriv bound), (VarTriv cur)] = rnds
                            {-
                            bck = [ C.BlockDecl [cdecl| $ty:(codegenTy ChunkTy) $id:new_chunk = gib_grow_region($id:bound); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:chunk_start = $id:new_chunk.start; |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:chunk_end = $id:new_chunk.end; |]
                                  , C.BlockStm  [cstm|  $id:bound = $id:chunk_end; |]
                                  , C.BlockStm  [cstm|  *($ty:(codegenTy TagTyPacked) *) ($id:cur) = GIB_REDIRECTION_TAG; |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) redir =  $id:cur + 1; |]
                                  , C.BlockStm  [cstm|  *($ty:(codegenTy CursorTy) *) redir = $id:chunk_start; |]
                                  , C.BlockStm  [cstm|  $id:cur = $id:chunk_start; |]
                                  ]
                        return [ C.BlockStm [cstm| if (($id:cur + $int:i) > $id:bound) { $items:bck }  |] ]
                              -}
                            bck = [ C.BlockStm  [cstm|  gib_grow_region_with_extra(& $id:cur, & $id:bound, $int:i); |] ]
                        pure [ C.BlockStm [cstm| if (($id:cur + $int:i) > $id:bound) { $items:bck }  |] ]
                     L2.OutputMutable -> do
                        let [(IntTriv i),(VarTriv bound), (VarTriv cur), (VarTriv mutbounds), (VarTriv mutcur)] = rnds
                            {-
                            bck = [ C.BlockDecl [cdecl| $ty:(codegenTy ChunkTy) $id:new_chunk = gib_grow_region($id:bound); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:chunk_start = $id:new_chunk.start; |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:chunk_end = $id:new_chunk.end; |]
                                  , C.BlockStm  [cstm|  $id:bound = $id:chunk_end; |]
                                  , C.BlockStm  [cstm|  *($ty:(codegenTy TagTyPacked) *) ($id:cur) = GIB_REDIRECTION_TAG; |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) redir =  $id:cur + 1; |]
                                  , C.BlockStm  [cstm|  *($ty:(codegenTy CursorTy) *) redir = $id:chunk_start; |]
                                  , C.BlockStm  [cstm|  $id:cur = $id:chunk_start; |]
                                  ]
                        return [ C.BlockStm [cstm| if (($id:cur + $int:i) > $id:bound) { $items:bck }  |] ]
                              -}
                            bck = [ C.BlockStm  [cstm|  gib_grow_region_with_extra($id:mutcur, $id:mutbounds, $int:i); |]
                                    , C.BlockStm  [cstm|  $id:bound = *($id:mutbounds); |]
                                    , C.BlockStm  [cstm|  $id:cur = *($id:mutcur); |]
                                  ]
                        pure [ C.BlockStm [cstm| if (($id:cur + $int:i) > $id:bound) { $items:bck }  |] ]
                     _ -> error "no other mode expected!"
                    

                 BoundsCheckVector -> do
                   --_new_chunk   <- gensym "new_chunk"
                   --_chunk_start <- gensym "chunk_start"
                   --_chunk_end   <- gensym "chunk_end"
                   ifConds <- mapM (\(ProdTriv [(IntTriv i),(VarTriv bound), (VarTriv cur), _]) -> 
                                           pure [cexp| ($id:cur + $int:i) > $id:bound |]
                                      ) rnds
                   ifBody <- mapM (\(ProdTriv [(IntTriv i), _, _, ProdTriv [(VarTriv b), (VarTriv c)]]) -> do
                                       {- TODO: VS: Maybe we should check loc too, but i think we desinged this such that it is 
                                        not needed! -}
                                      -- Audit : Assumption, in mutable case both loc and reg are mutable.
                                       let bty = M.lookup b venv
                                       case bty of 
                                            Just CursorTy -> pure [ C.BlockStm  [cstm|  gib_grow_region_with_extra(& $id:c, & $id:b, $int:i); |] ]
                                            Just MutCursorTy -> pure [ C.BlockStm  [cstm|  gib_grow_region_with_extra($id:c, $id:b, $int:i); |] ]
                                            _ -> error "Did not expect variable type in gib_grow_region!\n"
                                  ) rnds
                   ifBody_update <- mapM (\(ProdTriv [_, _, (VarTriv cur), ProdTriv [_, (VarTriv c)]]) -> do
                                       let cty = M.lookup c venv
                                       case cty of 
                                            Just CursorTy -> pure []
                                            Just MutCursorTy -> pure [ C.BlockStm  [cstm|  ($id:cur = *$id:c); |] ]
                                            _ -> error "Did not expect variable type in gib_grow_region!\n"
                                  ) rnds
                   let condExpr = foldr1 (\c1 c2 -> [cexp| $exp:c1 || $exp:c2 |]) ifConds
                   let ifBody_update' = concat ifBody_update
                   let ifBody' = (concat ifBody) ++ ifBody_update'
                   pure [ C.BlockStm [cstm| if ($exp:condExpr) { $items:ifBody' } |] ]

                 SizeOfPacked -> let [(sizeV,IntTy)] = bnds
                                     [(VarTriv startV), (VarTriv endV)] = rnds
                                 in pure
                                   [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:sizeV = ($ty:(codegenTy IntTy)) $id:endV - $id:startV; |] ]
                 SizeOfScalar -> let [(sizeV,IntTy)] = bnds
                                     [(VarTriv w)]   = rnds
                                 in pure
                                   [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:sizeV = ($ty:(codegenTy IntTy)) sizeof($id:w); |] ]

                 GetFirstWord ->
                  let [ptr] = rnds in
                  case bnds of
                    [(outV,outTy)] -> pure
                     [ C.BlockDecl [cdecl|
                            $ty:(codegenTy outTy) $id:outV =
                              * (( $ty:(codegenTy outTy) *) $(codegenTriv venv ptr));
                          |] ]
                    _ -> error $ "wrong number of return bindings from GetFirstWord: "++show bnds

                 SizeParam -> let [(outV,IntTy)] = bnds in pure
                      [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:outV = gib_get_size_param(); |] ]

                 PrintInt ->
                     let [arg] = rnds
                         printFmt = if gopt Opt_Int32 dflags then "%d" else "%ld"
                     in case bnds of
                       [(outV,ty)] -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = printf($string:printFmt, $(codegenTriv venv arg)); |] ]
                       [] -> pure [ C.BlockStm [cstm| printf($string:printFmt, $(codegenTriv venv arg)); |] ]
                       _ -> error $ "wrong number of return bindings from PrintInt: "++show bnds

                 PrintChar ->
                     let [arg] = rnds in
                     case bnds of
                       [(outV,ty)] -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = printf("%c", $(codegenTriv venv arg)); |] ]
                       [] -> pure [ C.BlockStm [cstm| printf("%c", $(codegenTriv venv arg)); |] ]
                       _ -> error $ "wrong number of return bindings from PrintInt: "++show bnds

                 PrintFloat ->
                     let [arg] = rnds in
                     case bnds of
                       [(outV,ty)] -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = printf("%.2f", $(codegenTriv venv arg)); |] ]
                       [] -> pure [ C.BlockStm [cstm| printf("%.2f", $(codegenTriv venv arg)); |] ]
                       _ -> error $ "wrong number of return bindings from PrintInt: "++show bnds

                 PrintBool ->
                     let [arg] = rnds in
                     case bnds of
                       [(outV,ty)] -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = printf("%d", $(codegenTriv venv arg)); |] ]
                       [] -> pure [ C.BlockStm [cstm| printf("%d", $(codegenTriv venv arg)); |] ]
                       _ -> error $ "wrong number of return bindings from PrintInt: "++show bnds

                 PrintSym ->
                     let [arg] = rnds in
                     case bnds of
                       [(outV,ty)] -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:outV = gib_print_symbol($(codegenTriv venv arg)); |] ]
                       [] -> pure [ C.BlockStm [cstm| gib_print_symbol($(codegenTriv venv arg)); |] ]
                       _ -> error $ "wrong number of return bindings from PrintSym: "++show bnds

                 PrintString str
                     | [] <- bnds, [] <- rnds -> pure [ C.BlockStm [cstm| printf( $string:str ); |] ]
                     | otherwise -> error$ "wrong number of args/return values expected from PrintString prim: "++show (rnds,bnds)

                 WritePackedFile fp tyc
                    | [inV] <- rnds -> do
                        -- Inputs to the copy function.
                        outreg <- gensym "outreg"
                        start_outreg <- gensym "start_outreg"
                        end_outreg <- gensym "end_outreg"
                        end_inreg <- gensym "end_inreg"
                        -- Output from the copy function.
                        end_outreg2 <- gensym "end_outreg2"
                        end_inreg2 <- gensym "end_inreg2"
                        copy_start <- gensym "copy_start"
                        copy_end <- gensym "copy_end"
                        copy_size <- gensym "copy_size"
                        let rnds2 = [VarTriv end_inreg, VarTriv end_outreg, VarTriv start_outreg, inV]
                            bnds2 = [(end_outreg2,CursorTy),(end_inreg2,CursorTy),(copy_start,CursorTy),(copy_end,CursorTy)]
                        call_copyfn <- codegenTail venv mutEndEnv fenv sort_fns (LetCallT False bnds2 (GL.mkCopySansPtrsFunName tyc) rnds2 (AssnValsT [] Nothing)) (ProdTy []) sync_deps
                        let tyfile = [cty| typename FILE |]
                            tysize = [cty| typename size_t |]
                        out_hdl <- gensym "out_hdl"
                        wrote <- gensym "wrote"
                        pure $
                           (if genGC
                            then [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy) $id:outreg = gib_alloc_region_on_heap(gib_get_biginf_init_chunk_size()); |] ]
                            else [ C.BlockDecl [cdecl| $ty:(codegenTy RegionTy) $id:outreg = gib_alloc_region_on_heap(gib_get_biginf_init_chunk_size()); |] ]) ++
                               [ C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:start_outreg = $id:outreg.start; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:end_outreg = $id:outreg.end; |]
                                 -- This would ideally be the *end* of the input region corresponding to inV
                                 -- but we have don't have at hand here. Passing in NULL is okay because this pointer
                                 -- is unused in the copy function.
                                 -- To get the actual end of the input region, we'll have to encode WritePackedFile as an
                                 -- expression (instead of a PrimAppE), and add the appropriate code in ThreadRegions.hs.
                                 -- Sticking with the hacky and less invasive approach for now.
                               , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:end_inreg = NULL; |]
                               ] ++ call_copyfn ++
                               [ C.BlockDecl [cdecl| $ty:tyfile *$id:out_hdl = fopen($string:fp, "wb"); |]
                               -- , _todo
                               -- , _todo
                               , C.BlockDecl [cdecl| $ty:tysize $id:copy_size = ($ty:(codegenTy IntTy)) ($id:copy_end - $id:copy_start); |]
                               , C.BlockDecl [cdecl| $ty:tysize $id:wrote = fwrite($id:copy_start, $id:copy_size, 1, $id:out_hdl); |]
                               , C.BlockStm [cstm| fclose($id:out_hdl); |]
                               , C.BlockStm [cstm| printf("Wrote: %s\n", $string:fp); |]
                               , C.BlockStm [cstm| gib_free_region($id:end_outreg); |]
                               , C.BlockStm [cstm| free($id:outreg); |]
                               ]
                    | otherwise -> error $ "WritePackedFile, wrong arguments "++show rnds++", or expected bindings "++show bnds

                 -- FINISHME: Codegen here depends on whether we are in --packed mode or not.
                 ReadPackedFile mfile tyc
                     | [] <- rnds, [(outV,_outT)] <- bnds -> do
                             let filename = case mfile of
                                              Just f  -> [cexp| $string:f |] -- Fixed at compile time.
                                              Nothing -> [cexp| gib_read_benchfile_param() |] -- Will be set by command line arg.
                                 unpackName = GL.mkUnpackerName tyc
                                 unpackcall = LetCallT False [(outV,PtrTy),(toVar "junk",CursorTy)]
                                                    unpackName [VarTriv (toVar "ptr")] (AssnValsT [] Nothing)

                                 mmap_size = varAppend outV "_size"

                                 mmapCode =
                                  [ C.BlockDecl[cdecl| int fd = open( $filename, O_RDONLY); |]
                                  , C.BlockStm[cstm| { if(fd == -1) { fprintf(stderr,"fopen failed\n"); abort(); }} |]
                                  , C.BlockDecl[cdecl| struct stat st; |]
                                  , C.BlockStm  [cstm| fstat(fd, &st); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:mmap_size = st.st_size;|]
                                  , C.BlockDecl[cdecl| $ty:(codegenTy CursorTy) ptr = ($ty:(codegenTy CursorTy)) mmap(0,st.st_size,PROT_READ,MAP_PRIVATE,fd,0); |]
                                  , C.BlockStm[cstm| { if(ptr==MAP_FAILED) { fprintf(stderr,"mmap failed\n"); abort(); }} |]
                                  ]
                             docall <- if isPacked
                                       -- In packed mode we eagerly FORCE the IO to happen before we start benchmarking:
                                       then pure [ C.BlockStm [cstm| { int sum=0; for(int i=0; i < st.st_size; i++) sum += ptr[i]; } |]
                                                 , C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:outV = ptr; |]]
                                       else codegenTail venv mutEndEnv fenv sort_fns unpackcall voidTy sync_deps
                             return $ mmapCode ++ docall
                     | otherwise -> error $ "ReadPackedFile, wrong arguments "++show rnds++", or expected bindings "++show bnds

                 ReadArrayFile mfile ty
                   | [] <- rnds, [(outV,_outT)] <- bnds -> do
                           let parse_in_c t = case t of
                                                IntTy   -> if gopt Opt_Int32 dflags then "%d" else "%ld"
                                                FloatTy -> "%f"
                                                CharTy  -> "%c"
                                                _ -> error $ "ReadArrayFile: Lists of type " ++ sdoc ty ++ " not allowed."

                           elem <- gensym "arr_elem"
                           fp <- gensym "fp"
                           line <- gensym "line"
                           len <- gensym "len"
                           read <- gensym "read"
                           line_num <- gensym "i"

                           (tmps, tmps_parsers, tmps_assns, tmps_decls) <-
                                 case ty of
                                     IntTy -> do
                                       one <- gensym "tmp"
                                       let assn = C.BlockStm [cstm| $id:elem = $id:one ; |]
                                       pure ([one], [parse_in_c ty], [ assn ], [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:one; |] ])
                                     FloatTy -> do
                                       one <- gensym "tmp"
                                       let assn = C.BlockStm [cstm| $id:elem = $id:one ; |]
                                       pure ([one], [parse_in_c ty], [ assn ], [ C.BlockDecl [cdecl| $ty:(codegenTy FloatTy) $id:one; |] ])
                                     CharTy -> do
                                       one <- gensym "tmp"
                                       let assn = C.BlockStm [cstm| $id:elem = $id:one ; |]
                                       pure ([one], [parse_in_c ty], [ assn ], [ C.BlockDecl [cdecl| $ty:(codegenTy CharTy) $id:one; |] ])
                                     ProdTy tys -> do
                                       vs <- mapM (\_ -> gensym "tmp") tys
                                       let decls = map (\(name, t) -> C.BlockDecl [cdecl| $ty:(codegenTy t) $id:name; |] ) (zip vs tys)
                                           parsers = map parse_in_c tys
                                           assns = map (\(v, i) ->
                                                           let field = "field" ++ (show i)
                                                           in C.BlockStm [cstm| $id:elem.$id:field = $id:v; |])
                                                   (zip vs [0..])
                                       pure (vs, parsers, assns, decls)
                                     _ -> error $ "ReadArrayFile: Lists of type " ++ sdoc ty ++ " not allowed."

                           let scanf_vars   = map (\v -> [cexp| &($id:v) |]) tmps
                               scanf_line = [cexp| $id:line |]
                               scanf_format = [cexp| $string:(L.intercalate " " tmps_parsers) |]
                               scanf_rator  = C.Var (C.Id "sscanf" noLoc) noLoc
                               scanf = C.FnCall scanf_rator (scanf_line : scanf_format : scanf_vars) noLoc

                           let (filename, filelength) = case mfile of
                                            Just (f, i)  -> ( [cexp| $string:f |]
                                                            , [cexp| $int:i |]) -- Fixed at compile time.
                                            Nothing -> ( [cexp| gib_read_arrayfile_param() |]
                                                       , [cexp| gib_read_arrayfile_length_param() |]) -- Will be set by command line arg.

                           return $
                                  [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy ty)) ($id:outV) = gib_vector_alloc($filelength, sizeof($ty:(codegenTy ty))); |]
                                  , C.BlockDecl [cdecl| $ty:(codegenTy ty) $id:elem; |]
                                  , C.BlockStm  [cstm| FILE *($id:fp); |]
                                  , C.BlockDecl [cdecl| char *($id:line) = NULL; |]
                                  , C.BlockStm [cstm| size_t ($id:len); |]
                                  , C.BlockStm [cstm| $id:len = 0; |]
                                  , C.BlockStm [cstm| ssize_t ($id:read); |]
                                  , C.BlockStm [cstm| $id:fp = fopen( $filename, "r"); |]
                                  , C.BlockStm [cstm| { if($id:fp == NULL) { fprintf(stderr,"fopen failed\n"); abort(); }} |]
                                  ] ++ tmps_decls ++
                                  [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:line_num = 0; |]
                                  , C.BlockStm [cstm| while(($id:read = getline(&($id:line), &($id:len), $id:fp)) != -1) {
                                                      int xxxx = $scanf;
                                                      $items:tmps_assns
                                                      gib_vector_inplace_update($id:outV, $id:line_num, &($id:elem));
                                                      $id:line_num++;
                                                    } |]
                                  ]

                   | otherwise -> error $ "ReadPackedFile, wrong arguments "++show rnds++", or expected bindings "++show bnds

                 MMapFileSize v -> do
                       let [(outV,IntTy)] = bnds
                           -- Must match with mmap_size set by ReadPackedFile
                           mmap_size = varAppend v "_size"
                       return [ C.BlockDecl[cdecl| $ty:(codegenTy IntTy) $id:outV = $id:mmap_size; |] ]

                 ParSync -> do
                    let e = [cexp| cilk_sync |]
                    return $ [ C.BlockStm [cstm| $exp:e; |] ] ++ (map snd sync_deps)

                 GetCilkWorkerNum -> do
                   let [(outV, IntTy)] = bnds
                   return $ [ C.BlockDecl [cdecl| int $id:outV = __cilkrts_get_worker_number(); |] ]

                 IsBig -> do
                   let [(outV, BoolTy)] = bnds
                       -- [i,arg] = rnds
                       -- e = [cexp| gib_is_big($(codegenTriv venv i), $(codegenTriv venv arg)) |]
                       e = [cexp| false |]
                   return $ [ C.BlockDecl [cdecl| $ty:(codegenTy BoolTy) $id:outV = $exp:e; |] ]

                 Gensym  -> do
                   let [(outV,SymTy)] = bnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy SymTy) $id:outV = gib_gensym(); |] ]

                 FreeSymTable -> return [C.BlockStm [cstm| gib_free_symtable(); |]]

                 VAllocP elty -> do
                   let ty1 = codegenTy (VectorTy elty)
                       [(outV,_)] = bnds
                       [i] = rnds
                       i' = codegenTriv venv i
                   tmp <- gensym "tmp"
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:tmp = sizeof( $ty:(codegenTy elty)); |]
                          , C.BlockDecl [cdecl| $ty:ty1 $id:outV = gib_vector_alloc($exp:i', $id:tmp); |]
                          ]

                 VFreeP _elty -> do
                   let [vec] = rnds
                   return [ C.BlockStm [cstm| gib_vector_free($(codegenTriv venv vec)); |] ]

                 VFree2P _elty -> do
                   let [vec] = rnds
                   return [ C.BlockStm [cstm| free($(codegenTriv venv vec)); |] ]

                 VNthP elty -> do
                   let ty1 = codegenTy elty
                       [(outV,_)] = bnds
                       [VarTriv ls, i] = rnds
                       i' = codegenTriv venv i
                   tmp <- gensym "tmp"
                   return [ C.BlockDecl [cdecl| $ty:ty1 *($id:tmp); |]
                          , C.BlockStm  [cstm| $id:tmp = ($ty:ty1 *) gib_vector_nth($id:ls,$exp:i'); |]
                          , C.BlockDecl [cdecl| $ty:ty1 $id:outV = *($id:tmp); |]
                          ]

                 VLengthP{} -> do
                   let [(v,IntTy)] = bnds
                       [VarTriv ls] = rnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:v = gib_vector_length($id:ls); |] ]

                 InplaceVUpdateP elty -> do
                   let [(outV,_)] = bnds
                       [VarTriv old_ls, i, x] = rnds
                       i' = codegenTriv venv i
                       xexp = [cexp| $exp:(codegenTriv venv x) |]
                   case x of
                     VarTriv{} ->
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_inplace_update($id:old_ls, $exp:i', &$exp:xexp); |] ]
                     ProdTriv{} ->
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_inplace_update($id:old_ls, $exp:i', &$exp:xexp); |] ]
                     IntTriv{} -> do
                        tmp <- gensym "tmp"
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:tmp = $exp:xexp; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_inplace_update($id:old_ls, $exp:i', &$id:tmp); |] ]
                     CharTriv{} -> do
                        tmp <- gensym "tmp"
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy CharTy) $id:tmp = $exp:xexp; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_inplace_update($id:old_ls, $exp:i', &$id:tmp); |] ]
                     FloatTriv{} -> do
                        tmp <- gensym "tmp"
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy FloatTy) $id:tmp = $exp:xexp; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_inplace_update($id:old_ls, $exp:i', &$id:tmp); |] ]
                     _ -> error $ "codegen: InplaceVUpdateP: " ++ sdoc x

                 VConcatP elty -> do
                   let [(outV,_)] = bnds
                       [ls] = rnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_concat($exp:(codegenTriv venv ls)); |]
                          ]

                 VSortP elty -> do
                   let [(outV,_)] = bnds
                       [VarTriv old_ls, VarTriv sort_fn] = rnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_sort($id:old_ls, $id:sort_fn); |] ]

                 InplaceVSortP elty -> do
                   let [(outV,_)] = bnds
                       [VarTriv old_ls, VarTriv sort_fn] = rnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_inplace_sort($id:old_ls, $id:sort_fn); |] ]

                 VSliceP elty -> do
                   let [(outV,_)] = bnds
                       [from, to, VarTriv old_ls] = rnds
                       from' = codegenTriv venv from
                       to' = codegenTriv venv to
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_slice($exp:from', $exp:to', $id:old_ls); |] ]

                 VMergeP elty -> do
                   let [(outV,_)] = bnds
                       [VarTriv ls1, VarTriv ls2] = rnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy (VectorTy elty)) $id:outV = gib_vector_merge($id:ls1, $id:ls2); |] ]

                 PDictAllocP _k _v -> return $
                                  [ C.BlockStm [cstm| printf("PDictAllocP todo\n"); |]
                                  , C.BlockStm [cstm| exit(1); |]
                                  ]

                 PDictInsertP _k _v -> return
                                   [ C.BlockStm [cstm| printf("PDictInsertP todo\n"); |]
                                   , C.BlockStm [cstm| exit(1); |]
                                   ]

                 PDictLookupP _k _v -> return
                                   [ C.BlockStm [cstm| printf("PDictLookupP todo\n"); |]
                                   , C.BlockStm [cstm| exit(1); |]
                                   ]

                 PDictHasKeyP _k _v -> return
                                   [ C.BlockStm [cstm| printf("PDictHasKeyP todo\n"); |]
                                   , C.BlockStm [cstm| exit(1); |]
                                   ]

                 PDictForkP _k _v -> return
                                 [ C.BlockStm [cstm| printf("PDictForkP todo\n"); |]
                                 , C.BlockStm [cstm| exit(1); |]
                                 ]

                 PDictJoinP _k _v -> return
                                 [ C.BlockStm [cstm| printf("PDictJoinP todo\n"); |]
                                 , C.BlockStm [cstm| exit(1); |]
                                 ]

                 LLAllocP elty -> do
                   let ty1 = codegenTy (ListTy elty)
                       [(outV,_)] = bnds
                   return [ C.BlockDecl [cdecl| $ty:ty1 $id:outV = gib_list_alloc(sizeof( $ty:(codegenTy elty))); |] ]

                 LLIsEmptyP _elty -> do
                   let [(outV,outTy)] = bnds
                       [ls] = rnds
                       ls' = codegenTriv venv ls
                       outTy' = codegenTy outTy
                   return [ C.BlockDecl [cdecl| $ty:outTy' $id:outV = gib_list_is_empty($exp:ls'); |] ]

                 LLConsP elty -> do
                   let [(outV,_)] = bnds
                       [x, VarTriv old_ls] = rnds
                       xexp = [cexp| $exp:(codegenTriv venv x) |]
                   case x of
                     VarTriv{} ->
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy (ListTy elty)) $id:outV = gib_list_cons(&$exp:xexp, $id:old_ls); |] ]
                     ProdTriv{} ->
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy (ListTy elty)) $id:outV = gib_list_cons(&$exp:xexp, $id:old_ls); |] ]
                     IntTriv{} -> do
                        tmp <- gensym "tmp"
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:tmp = $exp:xexp; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy (ListTy elty)) $id:outV = gib_list_cons(&$id:tmp, $id:old_ls); |] ]
                     FloatTriv{} -> do
                        tmp <- gensym "tmp"
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy FloatTy) $id:tmp = $exp:xexp; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy (ListTy elty)) $id:outV = gib_list_cons(&$id:tmp, $id:old_ls); |] ]
                     SymTriv{} -> do
                        tmp <- gensym "tmp"
                        return [ C.BlockDecl [cdecl| $ty:(codegenTy IntTy) $id:tmp = $exp:xexp; |]
                               , C.BlockDecl [cdecl| $ty:(codegenTy (ListTy elty)) $id:outV = gib_list_cons(&$id:tmp, $id:old_ls); |] ]
                     _ -> error $ "codegen: LLConsP: " ++ sdoc x

                 LLHeadP _elty -> do
                   let [(outV,outTy)] = bnds
                       [ls] = rnds
                       ls' = codegenTriv venv ls
                       outTy' = codegenTy outTy
                   tmp <- gensym "tmp"
                   return [ C.BlockDecl [cdecl| $ty:outTy' *($id:tmp); |]
                          , C.BlockStm  [cstm| $id:tmp = ($ty:outTy' *) gib_list_head($exp:ls'); |]
                          , C.BlockDecl [cdecl| $ty:outTy' $id:outV = *($id:tmp); |] ]

                 LLTailP _elty -> do
                  let [(outV,outTy)] = bnds
                      [ls] = rnds
                      ls' = codegenTriv venv ls
                      outTy' = codegenTy outTy
                  return [ C.BlockDecl [cdecl| $ty:outTy' $id:outV = gib_list_tail($exp:ls'); |] ]

                 LLFreeP _elty -> do
                  let [ls] = rnds
                      ls' = codegenTriv venv ls
                  return [ C.BlockStm [cstm| gib_list_free($exp:ls'); |] ]

                 LLFree2P _elty -> do
                  let [ls] = rnds
                      ls' = codegenTriv venv ls
                  return [ C.BlockStm [cstm| free($exp:ls'); |] ]

                 LLCopyP _elty -> do
                  let [(outV,outTy)] = bnds
                      [ls] = rnds
                      ls' = codegenTriv venv ls
                      outTy' = codegenTy outTy
                  return [ C.BlockDecl [cdecl| $ty:outTy' $id:outV = gib_list_copy($exp:ls'); |] ]


                 GetNumProcessors -> do
                   let [(outV,outTy)] = bnds
                   return [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = gib_get_num_processors(); |] ]

                 PrintRegionCount -> return [ C.BlockStm [cstm| gib_print_global_region_count(); |] ]

                 SSPush stk tycon -> do
                   let tycon_t = (C.Id (tycon ++ "_T") noLoc)
                       [VarTriv loc, VarTriv endloc] = rnds
                   case stk of
                     Write ->
                       return [ C.BlockStm [cstm| gib_shadowstack_push($id:writeShadowstack, $id:loc, $id:endloc, Stk, $id:tycon_t); |] ]
                     Read ->
                       return [ C.BlockStm [cstm| gib_shadowstack_push($id:readShadowstack, $id:loc, $id:endloc, Stk, $id:tycon_t); |] ]

                 SSPop stk -> do
                   let [VarTriv loc, VarTriv endloc] = rnds
                   return $
                     (case stk of
                        Write -> [ C.BlockStm [cstm| $id:shadowstackFrame = gib_shadowstack_pop($id:writeShadowstack); |] ]
                        Read -> [ C.BlockStm [cstm| $id:shadowstackFrame = gib_shadowstack_pop($id:readShadowstack); |] ]) ++
                     [ C.BlockStm [cstm| $id:loc = $id:shadowstackFrame->ptr; |]
                     , C.BlockStm [cstm| $id:endloc = $id:shadowstackFrame->endptr; |]]

                 Assert -> do
                   let [VarTriv _chk] = rnds
                       ifdef = "#ifdef _GIBBON_DEBUG"
                       endif = "#endif"
                   return [ C.BlockStm [cstm| $escstm:ifdef |]
                          -- , C.BlockStm [cstm| assert($id:chk); |]
                          , C.BlockStm [cstm| $escstm:endif |]
                          ]

                 BumpArenaRefCount{} -> error "codegen: BumpArenaRefCount not handled."
                 ReadInt{} -> error "codegen: ReadInt not handled."
                 
                 {- VS : TODO: This is very slow!! We should not allocate new arrays everytime.
                         Instead we should consider adding an extra function argument to each function.
                         This way, we just allocate once, instead of allocating multiple times.                  
                  -}
                 MakeCursorArray -> do 
                                    let [(outV, _outT)] = bnds
                                    --let outVtmp = toVar $ (fromVar outV) ++ "_tmp"
                                    let args = rnds
                                    let size = length args
                                    let initList = map (\exp -> C.ExpInitializer exp (noLoc)) (map (codegenTriv venv) args)
                                    --let arrayInit = [cdecl| $ty:(codegenTy CursorTy) $id:outVtmp[$int:size] = { $inits:initList }; |]
                                    let arrayInit = [cdecl| $ty:(codegenTy CursorTy) $id:outV[$int:size] = { $inits:initList }; |]
                                    --let arrayMalloc = [cdecl|  $ty:(codegenTy outT) $id:outV = gib_array_alloc($id:outVtmp, $int:size); |]
                                    --pure [C.BlockDecl arrayInit, C.BlockDecl arrayMalloc]
                                    pure [C.BlockDecl arrayInit]
                                    --let arrayInit = [cdecl| $ty:(codegenTy CursorTy) $id:outV[$int:size] = { $inits:initList }; |]
                                    -- let arrayMalloc = [cdecl|  $ty:(codegenTy outT) $id:outV = gib_array_alloc($id:outVtmp, $int:size); |]
                                    --pure [C.BlockDecl arrayInit]

                 IndexCursorArray -> do 
                                    let [(outV, outT)] = bnds
                                    let [ptr, idx] = rnds
                                    case outT of
                                      MutCursorTy -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = &$exp:(codegenTriv venv ptr)[$exp:(codegenTriv venv idx)]; |] ]
                                      _ -> pure [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $exp:(codegenTriv venv ptr)[$exp:(codegenTriv venv idx)]; |] ]

                 --AddP -> let [(outV,outT)] = bnds
                 --            [pleft,pright] = rnds in pure
                 --        [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = $(codegenTriv venv pleft) + $(codegenTriv venv pright); |] ]

                 CastPtr -> do
                    let [(outV, outT)] = bnds
                        --outT' = case outT of 
                        --             CursorArrayTy{} -> MutCursorTy
                        --             _ -> outT
                        [ptr] = rnds
                        ptr' = codegenTriv venv ptr
                    case outT of 
                        CursorArrayTy{} -> do 
                                            -- In case it is a cusory array, we need to do an additional memcpy
                                            let init_array = C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV; |]
                                            -- C.BlockStm  [cstm| memcpy($id:x, $exp:y, sizeof($ty:t)); |]
                                            -- return [ init_array, C.BlockStm [cstm| memcpy($id:outV, ($ty:(codegenTy outT)) $exp:ptr', sizeof($ty:(codegenTy outT))) ;|] ]
                                            return [ init_array, C.BlockStm [cstm| memcpy($id:outV, $exp:ptr', sizeof($ty:(codegenTy outT))) ;|] ] 
                        _ -> return [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = ($ty:(codegenTy outT)) $exp:ptr'; |] ] 
                    
                  
                 AddrOfCursor -> do
                    let [(outV, outT)] = bnds
                        [expr] = rnds 
                        expr' = codegenTriv venv expr
                    case expr of 
                        IndexCursorArrayTriv{} -> do 
                          case outT of
                                MutCursorTy -> if L.isPrefixOf "end" (fromVar outV)
                                               then return [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = &($exp:expr'); |] ]
                                               else return [ C.BlockDecl [cdecl| typename GibCursor * restrict $id:outV = &($exp:expr'); |] ]
                                -- add other Ty cases here if they also mean GibCursor*
                                _ ->
                                  return [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = &($exp:expr'); |] ]
                        VarTriv v ->
                          return [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = &($id:v); |] ]
                        _ -> do 
                             tmp <- gensym "tmp_copy"
                             return [ 
                              C.BlockDecl [cdecl| $ty:(codegenTy CursorTy) $id:tmp =  $exp:expr'; |],
                              C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV =  &($id:tmp); |] ]

                 DerefMutCursor -> do 
                    let [(outV, outT)] = bnds
                        [var] = rnds
                        var' = codegenTriv venv var
                    return [ C.BlockDecl [cdecl| $ty:(codegenTy outT) $id:outV = *($exp:var'); |] ]



       return $ pre ++ bod'

codegenTail _ _ _ _ (Goto lbl) _ty _ = do
  return [ C.BlockStm [cstm| goto $id:lbl; |] ]

-- | The sizes for all mulitplicities are defined as globals in the RTS.
-- Note: Must be consistent with the names in RTS!
codegenMultiplicity :: Multiplicity -> C.Exp
codegenMultiplicity mul =
  case mul of
    BigInfinite -> [cexp| gib_get_biginf_init_chunk_size() |]
    Infinite    -> [cexp| gib_get_inf_init_chunk_size() |]
    Bounded i   ->
      let rounded = i+18
      in [cexp| $int:rounded |]

-- | Round up a number to a power of 2.
--
-- Copied from https://stackoverflow.com/a/466256.
roundUp :: Int -> Int
roundUp n = ceiling (2 ^ (ceiling (log (fromIntegral n) / log 2)))

splitAlts :: Alts -> (Alts, Alts)
splitAlts (TagAlts ls) = (TagAlts (L.init ls), TagAlts [last ls])
splitAlts (IntAlts ls) = (IntAlts (L.init ls), IntAlts [last ls])

-- | Take a "singleton" Alts and extract the Tail.
altTail :: Alts -> Tail
altTail (TagAlts [(_,t)]) = t
altTail (IntAlts [(_,t)]) = t
altTail oth = error $ "altTail expected a 'singleton' Alts, got: "++ abbrv 80 oth


-- Helper for lhs of a case
mk_tag_lhs :: (Integral a, Show a) => a -> C.Exp
mk_tag_lhs lhs
    | GL.indirectionAlt == lhs = C.Var (C.Id "GIB_INDIRECTION_TAG" noLoc) noLoc
    | GL.redirectionAlt == lhs = C.Var (C.Id "GIB_REDIRECTION_TAG" noLoc) noLoc
    | otherwise = C.Const (C.IntConst (show lhs) C.Unsigned (fromIntegral lhs) noLoc) noLoc

mk_int_lhs :: (Integral a, Show a) => a -> C.Exp
mk_int_lhs lhs = C.Const (C.IntConst (show lhs) C.Signed   (fromIntegral lhs) noLoc) noLoc

normalizeAlts :: Alts -> [(C.Exp, Tail)]
normalizeAlts alts =
    case alts of
      TagAlts as -> map (first mk_tag_lhs) as
      IntAlts as -> map (first mk_int_lhs) as

-- | Generate a proper switch expression instead.
genSwitch :: VEnv -> MutEndEnv -> FEnv -> S.Set Var -> Label -> Triv -> Alts -> Tail -> Ty -> SyncDeps -> PassM [C.BlockItem]
genSwitch venv mutEndEnv fenv sort_fns lbl tr alts lastE ty sync_deps =
    do let go :: [(C.Exp,Tail)] -> PassM [C.Stm]
           go [] = do tal <- codegenTail venv mutEndEnv fenv sort_fns lastE ty sync_deps
                      return [[cstm| default: $stm:(mkBlock tal) |]]
           go ((ex,tl):rst) =
               do tal <- codegenTail venv mutEndEnv fenv sort_fns tl ty sync_deps
                  let tal2 = tal ++ [ C.BlockStm [cstm| break; |] ]
                  let this = [cstm| case $exp:ex : $stm:(mkBlock tal2) |]
                  rst' <- go rst
                  return (this:rst')
       alts' <- go (normalizeAlts alts)
       let body = mkBlock [ C.BlockStm a | a <- alts' ]
       return $ [ C.BlockStm [cstm| $id:lbl: ; |]
                , C.BlockStm [cstm| switch ( $exp:(codegenTriv venv tr) ) $stm:body |]]

-- | The identifier after typename refers to typedefs defined in rts.c
--

codegenVecBroadcast :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecBroadcast venv bnds scalar lanes rnds = do
  when (length bnds /= 1 || length rnds /= 1) $
    error $ "VecBroadcast expected one binding and one arg: " ++ show (bnds, rnds)
  let [(outV, outTy)] = bnds
      [val] = rnds
      fn = vecHelperName "broadcast" scalar lanes
  pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = $id:fn($(codegenTriv venv val)); |] ]

codegenVecLoad :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecLoad _venv bnds scalar lanes rnds = do
  when (length bnds /= 1 || length rnds /= 1) $
    error $ "VecLoad expected one binding and one arg: " ++ show (bnds, rnds)
  let [(outV, outTy)] = bnds
      [refTriv] = rnds
      fn = vecHelperName "load" scalar lanes
  ref <- case refTriv of
           VarTriv v -> pure v
           _ -> error $ "VecLoad expected cursor ref variable: " ++ show refTriv
  pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = $id:fn($id:ref); |] ]

codegenVecAdd :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecAdd = codegenVecBin "add" "VecAdd"

codegenVecSub :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecSub = codegenVecBin "sub" "VecSub"

codegenVecMul :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecMul = codegenVecBin "mul" "VecMul"

codegenVecDiv :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecDiv = codegenVecBin "div" "VecDiv"

codegenVecMod :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecMod = codegenVecBin "mod" "VecMod"

codegenVecEq :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecEq = codegenVecBin "eq" "VecEq"

codegenVecBin :: String -> String -> M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecBin op label venv bnds scalar lanes rnds = do
  when (length bnds /= 1 || length rnds /= 2) $
    error $ label ++ " expected one binding and two args: " ++ show (bnds, rnds)
  let [(outV, outTy)] = bnds
      [lhs, rhs] = rnds
      fn = vecHelperName op scalar lanes
  pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = $id:fn($(codegenTriv venv lhs), $(codegenTriv venv rhs)); |] ]

codegenVecSelect :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecSelect venv bnds scalar lanes rnds = do
  when (length bnds /= 1 || length rnds /= 3) $
    error $ "VecSelect expected one binding and three args: " ++ show (bnds, rnds)
  let [(outV, outTy)] = bnds
      [mask, thenv, elsev] = rnds
      fn = vecHelperName "select" scalar lanes
  pure [ C.BlockDecl [cdecl| $ty:(codegenTy outTy) $id:outV = $id:fn($(codegenTriv venv mask), $(codegenTriv venv thenv), $(codegenTriv venv elsev)); |] ]

codegenVecStore :: M.Map Var Ty -> [(Var, Ty)] -> Scalar -> Int -> [Triv] -> PassM [C.BlockItem]
codegenVecStore venv bnds scalar lanes rnds = do
  when (not (null bnds) || length rnds /= 2) $
    error $ "VecStore expected no bindings and two args: " ++ show (bnds, rnds)
  let [refTriv, val] = rnds
      fn = vecHelperName "store" scalar lanes
  ref <- case refTriv of
           VarTriv v -> pure v
           _ -> error $ "VecStore expected cursor ref variable: " ++ show refTriv
  pure [ C.BlockStm [cstm| $id:fn($id:ref, $(codegenTriv venv val)); |] ]

vecHelperName :: String -> Scalar -> Int -> Var
vecHelperName op scalar lanes
  | vecOpSupported op scalar lanes = toVar $ "gib_vec_" ++ op ++ "_" ++ scalarSuffix scalar lanes
  | otherwise = error $ "Unsupported SIMD operation/scalar/lane combination: " ++ show (op, scalar, lanes)

vecOpSupported :: String -> Scalar -> Int -> Bool
vecOpSupported op scalar lanes =
  case op of
    "broadcast" -> scalarSuffixSupported scalar lanes
    "load" -> scalarSuffixSupported scalar lanes
    "store" -> scalarSuffixSupported scalar lanes
    "add" -> scalarSuffixSupported scalar lanes
    "sub" -> scalarSuffixSupported scalar lanes
    "mul" -> (scalar == FloatS && lanes == 4) || (scalar == IntS && lanes `elem` [2,4])
    "div" -> (scalar == FloatS && lanes == 4) || (scalar == IntS && lanes `elem` [2,4])
    "mod" -> scalar == IntS && lanes `elem` [2,4]
    "eq" -> (scalar == FloatS && lanes == 4) || (scalar == IntS && lanes `elem` [2,4])
    "select" -> (scalar == FloatS && lanes == 4) || (scalar == IntS && lanes `elem` [2,4])
    _ -> False

scalarSuffixSupported :: Scalar -> Int -> Bool
scalarSuffixSupported scalar lanes =
  case (scalar, lanes) of
    (IntS, 2) -> True
    (IntS, 4) -> True
    (SymS, 2) -> True
    (CharS, 16) -> True
    (BoolS, 16) -> True
    (FloatS, 4) -> True
    _ -> False

scalarSuffix :: Scalar -> Int -> String
scalarSuffix IntS 2 = "int64x2"
scalarSuffix IntS 4 = "int32x4"
scalarSuffix SymS 2 = "sym64x2"
scalarSuffix CharS 16 = "char8x16"
scalarSuffix BoolS 16 = "bool8x16"
scalarSuffix FloatS 4 = "float32x4"
scalarSuffix scalar lanes = error $ "Unsupported SIMD scalar/lane combination: " ++ show (scalar, lanes)

codegenTy :: Ty -> C.Type
codegenTy IntTy = [cty|typename GibInt|]
codegenTy CharTy = [cty|typename GibChar|]
codegenTy FloatTy= [cty|typename GibFloat|]
codegenTy BoolTy = [cty|typename GibBool|]
codegenTy TagTyPacked = [cty|typename GibPackedTag|]
codegenTy TagTyBoxed  = [cty|typename GibBoxedTag|]
codegenTy SymTy = [cty|typename GibSym|]
codegenTy PtrTy = [cty|typename GibPtr|] -- char* - Hack, this could be void* if we have enough casts. [2016.11.06]
codegenTy CursorTy = [cty|typename GibCursor|]
codegenTy (CursorArrayTy size) = [cty| typename GibCursor[$int:size] |]
codegenTy MutCursorTy = [cty|typename GibCursor*|]
codegenTy (SimdTy IntTy 2) = [cty|typename __m128i|]
codegenTy (SimdTy IntTy 4) = [cty|typename __m128i|]
codegenTy (SimdTy SymTy 2) = [cty|typename __m128i|]
codegenTy (SimdTy CharTy 16) = [cty|typename __m128i|]
codegenTy (SimdTy BoolTy 16) = [cty|typename __m128i|]
codegenTy (SimdTy FloatTy 4) = [cty|typename __m128|]
codegenTy (SimdTy ty lanes) = error $ "Unsupported SIMD register type in codegen: " ++ show (ty, lanes)
codegenTy RegionTy = [cty|typename GibChunk|]
codegenTy ChunkTy = [cty|typename GibChunk|]
codegenTy (ProdTy []) = [cty|unsigned char|]
codegenTy (ProdTy ts) = C.Type (C.DeclSpec [] [] (C.Tnamed (C.Id nam noLoc) [] noLoc) noLoc) (C.DeclRoot noLoc) noLoc
    where nam = makeName ts
codegenTy (SymDictTy _ _t) = [cty|typename GibSymDict|]
codegenTy SymSetTy = [cty|typename GibSymSet*|]
codegenTy SymHashTy = [cty|typename GibSymHash*|]
codegenTy IntHashTy = [cty|typename GibIntHash*|]
codegenTy ArenaTy = [cty|typename GibArena*|]
codegenTy VectorTy{} = [cty|typename GibVector* |]
codegenTy ListTy{} = [cty|typename GibList* |]
codegenTy PDictTy{} = [cty|typename GibPDict* |]

makeName :: [Ty] -> String
makeName tys = concatMap makeName' tys ++ "Prod"

makeName' :: Ty -> String
makeName' IntTy       = "GibInt"
makeName' CharTy      = "GibChar"
makeName' FloatTy     = "GibFloat"
makeName' SymTy       = "GibSym"
makeName' BoolTy      = "GibBool"
makeName' CursorTy    = "GibCursor"
makeName' (CursorArrayTy sz) = "GibCursorPtr" ++ show sz
makeName' (MutCursorTy) = "GibMutCursor"
makeName' (SimdTy ty lanes) = "GibSimd" ++ show lanes ++ makeName' ty
makeName' TagTyPacked = "GibPackedTag"
makeName' TagTyBoxed  = "GibBoxedTag"
makeName' PtrTy       = "GibPtr"
makeName' (SymDictTy _ _ty) = "GibSymDict"
makeName' RegionTy = "GibChunk"
makeName' ChunkTy  = "GibChunk"
makeName' ArenaTy  = "GibArena"
makeName' VectorTy{} = "GibVector"
makeName' ListTy{} = "GibList"
makeName' PDictTy{} = "PDict"
makeName' (ProdTy tys) = "Prod" ++ concatMap makeName' tys
makeName' SymSetTy = "GibSymSet"
makeName' SymHashTy = "GibSymHash"
makeName' IntHashTy = "GibIntHash"


makeIcdName :: Ty -> (String, String)
makeIcdName ty =
  let ty_name  =
        case ty of
          IntTy      -> "IntTy"
          FloatTy    -> "FloatTy"
          BoolTy     -> "BoolTy"
          SymTy      -> "SymTy"
          ProdTy tys -> makeName tys
          _ -> "codegenTail: Lists of type " ++ sdoc ty ++ " not allowed."
      icd_name = ty_name ++ "_icd"
  in (ty_name, icd_name)


mkBlock :: [C.BlockItem] -> C.Stm
mkBlock ss = C.Block ss noLoc

cid :: Var -> C.Exp
cid v = C.Var (C.toIdent v noLoc) noLoc

toStmt :: C.Exp -> C.BlockItem
toStmt x = C.BlockStm [cstm| $exp:x; |]

-- toMemCpyStmt :: C.Exp -> C.BlockItem 
-- toMemCpyStmt x = C.BlockStm  [cstm| memcpy($id:x, $exp:y, sizeof($ty:t)); |]

-- | Create a NEW lexical binding.
assn :: (C.ToIdent v, C.ToExp e) => C.Type -> v -> e -> C.BlockItem
assn t x y = C.BlockDecl [cdecl| $ty:t $id:x = $exp:y; |]

-- initVar :: (C.ToIdent v) => C.Type -> v -> C.BlockItem
-- initVar t x = C.BlockDecl [cdecl| $ty:t $id:x; |]

initVarItems :: (C.ToIdent v, C.ToExp e) => C.Type -> v -> e -> [C.BlockItem]
initVarItems t x y =
  [ C.BlockDecl [cdecl| $ty:t $id:x; |]
  , C.BlockStm  [cstm| memcpy($id:x, $exp:y, sizeof($ty:t)); |]
  ]
 
-- | Mutate an existing binding:
mut :: (C.ToIdent v, C.ToExp e) => C.Type -> v -> e -> C.BlockItem
mut _t x y = C.BlockStm [cstm| $id:x = $exp:y; |]

memcpy :: (C.ToIdent v, C.ToExp e) => C.Type -> v -> e -> C.BlockItem
memcpy t x y = C.BlockStm  [cstm| memcpy($id:x, $exp:y, sizeof($ty:t)); |]
