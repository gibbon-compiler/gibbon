{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}

-- |  Parse an SExp representaton of our tree-walk language.

module Gibbon.SExpFrontend
       ( parseFile
       , parseSExp
       , primMap )
  where

import Control.Monad
import Data.Char ( isLower, isAlpha )
import Data.List as L
import Data.Loc
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Text hiding (map, head, init, last, length, zip)
import qualified Data.Text as T
import Data.Text.IO (readFile)
import System.FilePath
import Text.Parsec
import Text.PrettyPrint.GenericPretty
import Prelude hiding (readFile, exp)

-- There are several options for s-expression parsing, including these
-- packages on Hackage:
--  * sexp
--  * sexpr
--  * sexp-grammar
--  * atto-lisp
--  * lispparser
-- Using 's-cargo' for the first attempt:
import Data.SCargot.Language.HaskLike
import Data.SCargot.Parse
import Data.SCargot.Print
import Data.SCargot.Repr -- (SExpr, RichSExpr, toRich)
import qualified Data.SCargot.Common as SC

import Gibbon.L0.Syntax
import Gibbon.Common

--------------------------------------------------------------------------------

-- | Baseline chatter level for this module:
lvl :: Int
lvl = 5

deriving instance Generic (SExpr a)
deriving instance Generic (RichSExpr a)
deriving instance Generic HaskLikeAtom
instance (Generic a, Out a) => Out (SExpr a)
instance (Generic a, Out a) => Out (RichSExpr a)
instance Out HaskLikeAtom
instance Out Text where
  doc t = doc (T.unpack t)
  docPrec n t = docPrec n (T.unpack t)

type Sexp = RichSExpr (SC.Located HaskLikeAtom)

prnt :: Sexp -> String
prnt = T.unpack . encodeOne locatedHaskLikePrinter . fromRich

textToVar :: Text -> Var
textToVar = toVar . T.unpack

textToDataCon :: Text -> DataCon
textToDataCon = T.unpack

-- | Convert Location (s-cargot) to Loc (Data.Loc)
-- s-cargot uses SrcPos exported by Parsec whereas Data.Loc has it's own notion of Pos
toLoc :: SC.Location -> Loc
toLoc (SC.Span start end) = Loc (toPos start) (toPos end)

toPos :: SourcePos -> Pos
toPos sp = Pos name line col 0
  where name = sourceName sp
        line = sourceLine sp
        col  = sourceColumn sp

loc :: SC.Location -> a -> L a
loc l = L (toLoc l)

-- Ideally, we'd extend the parser to ignore #lang lines.
-- But for now we'll just do that in a preprocessing hack.
treelangParser :: SExprParser (SC.Located HaskLikeAtom) (SExpr (SC.Located  HaskLikeAtom))
treelangParser =
    let langline = string "#lang " *> eatline
        comment  = string ";"      *> eatline
        eatline  = manyTill anyChar newline *> pure ()
        quote expr     = SCons (SAtom "quote") (SCons expr SNil)
        addQuoteReader = addReader '\'' (\ parse -> fmap quote parse)
    in
    -- setCarrier (return . asRich) $
        setComment (comment <|> langline) $
        addQuoteReader locatedHaskLikeParser

-- Hack:
_stripHashLang :: Text -> Text
_stripHashLang txt =
  if T.isPrefixOf "#lang" txt
  then snd $ T.break (== '\n') txt
       -- (\c -> generalCategory c == LineSeparator)
  else txt

bracketHacks :: Text -> Text
bracketHacks = T.map $ \case '[' -> '('
                             ']' -> ')'
                             x   -> x

-- | Change regular applications into data constructor syntax.
tagDataCons :: DDefs Ty0 -> L Exp0 -> PassM (L Exp0)
tagDataCons ddefs = go allCons
  where
   allCons = S.fromList [ (toVar con)
                        | DDef{dataCons} <- M.elems ddefs
                        , (con,_tys) <- dataCons ]

   go :: S.Set Var -> L Exp0 -> PassM (L Exp0)
   go cons (L p ex) = L p <$>
     case ex of
       Ext _ -> pure ex
       -- [2019.02.01] CSK: Do we need this special case ?
       AppE v _ ls
                  | S.member v cons -> do
                      ty <- newMetaTy
                      DataConE ty (fromVar v) <$> (mapM (go cons) ls)
       AppE v l ls | S.member v cons -> do ty <- newMetaTy
                                           DataConE ty (fromVar v) <$> mapM (go cons) ls
                   | otherwise       -> AppE v l <$> mapM (go cons) ls
       LetE (v,l,t,rhs) bod -> do
         let go' = if S.member v cons
                      then go (S.delete v cons)
                      else go cons
         LetE <$> (v,l,t,) <$> go' rhs <*> (go' bod)
       ------------boilerplate------------
       VarE{}          -> pure ex
       LitSymE{}       -> pure ex
       LitE _          -> pure ex
       PrimAppE p ls   -> PrimAppE p <$> mapM (go cons) ls
       ProjE i e  -> ProjE i <$> (go cons e)
       CaseE e ls -> CaseE <$> (go cons e) <*> (mapM (\(c,vs,er) -> (c,vs,) <$> go cons er) ls)
       MkProdE ls     -> MkProdE <$> mapM (go cons) ls
       DataConE loc k ls -> DataConE loc k <$> mapM (go cons) ls
       TimeIt e t b -> do e' <- (go cons e)
                          pure $ TimeIt e' t b
       IfE a b c -> IfE <$> (go cons a) <*> (go cons b) <*> (go cons c)
       WithArenaE v e -> WithArenaE v <$> (go cons e)

       MapE  (v,t,e) bod -> MapE <$> (v,t, ) <$> go cons e <*> (go cons bod)
       FoldE (v1,t1,e1) (v2,t2,e2) b -> do
         e1' <- go cons e1
         e2' <- go cons e2
         b'  <- go cons b
         pure $ FoldE (v1,t1,e1') (v2,t2,e2') b'
       SpawnE{} -> error "tagDataCons: SpawnE not handled"
       SyncE{} -> error "tagDataCons: SyncE not handled"
       IsBigE{} -> error "tagDataCons: IsBigE not handled"

-- | Convert from raw, unstructured S-Expression into the L1 program datatype we expect.
parseSExp :: [Sexp] -> PassM Prog0
parseSExp ses = do
  prog@Prog {ddefs} <- go ses [] [] [] Nothing
  mapMExprs (tagDataCons ddefs) prog
 where

   -- WARNING: top-level constant definitions are INLINED everywhere.
   inlineConstDefs [] p = p
   inlineConstDefs ((vr,_ty,rhs) : cds) p =
       inlineConstDefs cds $
        mapExprs (subst vr rhs) p

   -- Processes an sexpression while accumulating data, function, and constant defs.
   go xs dds fds cds mn =
    case xs of
     [] -> return $
           inlineConstDefs cds $
           Prog (fromListDD dds) (fromListFD fds) mn

     -- IGNORED!:
     (Ls (A _ "provide":_) : rst) -> go rst dds fds cds mn
     (Ls (A _ "require":_) : rst) -> go rst dds fds cds mn

{-

Polymorphic datatypes:

    (data PolyD (a b) [K3 ... a b ...])

While parsing datatypes with type variables, 'isTyVar' decides
if a thing is a type variable or a data constructor.

-}
     (Ls (A _ "data": A _ tycon  : cs) : rst) -> do
       let tycon' = textToVar tycon
       case cs of
         [] -> go rst ((DDef tycon' [] []) : dds) fds cds mn
         (Ls k) : ks ->
           case k of
             [] -> go rst ((DDef tycon' [] (L.map docasety cs)) : dds) fds cds mn
             (A _ tyvar_or_constr : _) ->
               if isTyVar tyvar_or_constr
               then do let tyargs = L.map (UserTv . getSym) k
                       go rst (DDef (textToVar tycon) tyargs (L.map docasety ks) : dds) fds cds mn
               else go rst (DDef (textToVar tycon) [] (L.map docasety cs) : dds) fds cds mn
             _ -> error $ "Unexpected constructor while parsing data: " ++ show k
         _ -> error $ "Unexpected constructors while parsing data: " ++ show cs

     (Ls [A _ "define", funspec, A _ ":", retty, bod] : rst)
         |  RSList (A _ name : args) <- funspec
        -> do
         bod' <- exp bod
         let args' = L.map (\(RSList [id, A _ ":",t]) -> (getSym id, typ t)) args
             (args'', arg_tys) = unzip args'
         let fun_ty = ArrowTy arg_tys (typ retty)
         go rst dds (FunDef { funName = textToVar name
                            , funArgs = args''
                            , funTy   = ForAll (tyVarsInTy fun_ty) fun_ty
                            , funBody = bod'
                            } : fds)
            cds mn

     -- Top-level definition instead of a function.
     (Ls [A _ "define", A _ topid, A _ ":", ty, bod] : rst) -> do
       bod' <- exp bod
       go rst dds fds ((textToVar topid,ty,bod') : cds) mn

     (Ls [A _ "define", _args, _bod] : _) -> error$ "Function is missing return type:\n  "++prnt (head xs)
     (Ls (A _ "define" : _) : _) -> error$ "Badly formed function:\n  "++show (head xs)

     (Ls (A _ "data" : _) : _) -> error$ "Badly formed data definition:\n  "++prnt (head xs)

     (Ls3 _ "module+" _ bod : rst) -> go (bod:rst) dds fds cds mn

     (ex : rst) -> do
       ex' <- exp ex
       ty  <- newMetaTy
       go rst dds fds cds (case mn of
                                -- Initialize the main expression with a void type.
                                -- The typechecker will fix it later.
                                Nothing -> Just (ex', ty)
                                Just x  -> error$ "Two main expressions: "++
                                                 sdoc x++"\nAnd:\n"++prnt ex)

typ :: Sexp -> Ty0
typ s = case s of
         (A _ "Int")  -> IntTy
         (A _ "Sym")  -> SymTy0
         (A _ "SymSet") -> SymSetTy
         (A _ "SymHash") -> SymHashTy
         (A _ "Bool") -> BoolTy
         (A _ "Arena") -> ArenaTy
         -- If it's lowercase, it's a type variable. Otherwise, a Packed type.
         (A _ con)    -> if isTyVar con
                         then TyVar $ UserTv (textToVar con)
                         else PackedTy (textToDataCon con) []
         (Ls3 _ "SymDict" (A _ v) t) -> SymDictTy (Just (textToVar v)) (typ t)
         (Ls2 _ "Listof" t)  -> ListTy $ typ t
         -- See https://github.com/aisamanra/s-cargot/issues/14.
         (Ls (A _ "-" : A _ ">" : tys)) ->
             let tys'   = L.map typ tys
             in ArrowTy (init tys') (last tys')
         (Ls (A _ "Vector"  : rst)) -> ProdTy $ L.map typ rst
         (Ls (A _ tycon : tyargs))  -> PackedTy (textToDataCon tycon) (L.map typ tyargs)
         _ -> error$ "SExpression encodes invalid type:\n "++ show s

-- Some text is a tyvar if it starts with a lowercase alphabet.
isTyVar :: Text -> Bool
isTyVar t = isLower h && isAlpha h
  where h = T.head t

getSym :: Sexp -> Var
getSym (A _ id) = textToVar id
getSym s = error $ "expected identifier sexpr, got: "++prnt s

docasety :: Sexp -> (DataCon,[(IsBoxed,Ty0)])
docasety s =
  case s of
    (RSList ((A _ id) : tys)) -> (textToDataCon id, L.map ((False,) . typ) tys)
    _ -> error$ "Badly formed variant of datatype:\n "++prnt s

pattern A loc s = RSAtom (SC.At loc (HSIdent s))
pattern G loc s = RSAtom (SC.At loc s)
pattern Ls a              = RSList a
pattern Ls1 a             = RSList [a]
pattern Ls2 loc a b       = RSList [A loc a, b]
pattern Ls3 loc a b c     = RSList [A loc a, b, c]
pattern Ls4 loc a b c d   = RSList [A loc a, b, c, d]
pattern Ls5 loc a b c d e = RSList [A loc a, b, c, d, e]
-- pattern L5 a b c d e = RSList [A a, b, c, d, e]

trueE :: Exp0
trueE = PrimAppE MkTrue []

falseE :: Exp0
falseE = PrimAppE MkFalse []

-- -- FIXME: we cannot intern strings until runtime.
-- hackySymbol :: String -> Int
-- hackySymbol s = product (L.map ord s)

keywords :: S.Set Text
keywords = S.fromList $ L.map pack $
           [ "quote", "if", "or", "and", "time", "let", "let*"
           , "case", "vector-ref", "for/fold", "for/list"
           , "insert", "empty-dict", "lookup", "error", "ann"
           , "div", "mod", "exp", "rand"
           ]

isKeyword :: Text -> Bool
isKeyword s = s `S.member` keywords

exp :: Sexp -> PassM (L Exp0)
exp se =
 case se of
   A l "True"  -> pure $ L (toLoc l) trueE
   A l "False" -> pure $ L (toLoc l) falseE

   Ls ((A l "and") : args)  -> go args
     where
       go :: [Sexp] -> PassM (L Exp0)
       go [] = pure $ loc l trueE
       go (x:xs) = do
         x'  <- exp x
         xs' <- go xs
         pure $ loc l $ IfE x' xs' (L NoLoc falseE)

   Ls ((A l "or") : args)  -> go args
     where
       go :: [Sexp] -> PassM (L Exp0)
       go [] = pure $ loc l falseE
       go (x:xs) = do
         x'  <- exp x
         xs' <- go xs
         pure $ loc l $ IfE x' (L NoLoc trueE) xs'

   Ls4 l "if" test conseq altern -> do
     e' <- IfE <$> (exp test) <*> (exp conseq) <*> (exp altern)
     pure $ loc l $ e'

   Ls2 l "quote" (A _ v) -> pure $ loc l $ LitSymE (textToVar v)

   -- Any other naked symbol is a variable:
   A l v          -> pure $ loc l $ VarE (textToVar v)
   G l (HSInt n)  -> pure $ loc l $ LitE (fromIntegral n)

   -- This type gets replaced later in flatten:
   Ls2 l "time" arg -> do
     ty <- newMetaTy
     arg' <- exp arg
     pure $ loc l $ TimeIt arg' ty False

   Ls3 l "bench" (A _ fn) arg -> do
     arg' <- exp arg
     pure $ loc l $ Ext $ BenchE (textToVar fn) [] [arg'] False

   -- This variant inserts a loop, controlled by the iters
   -- argument on the command line.
   Ls2 l "iterate" arg -> do
     ty <- newMetaTy
     arg' <- exp arg
     pure $ loc l $ TimeIt arg' ty True

   Ls3 l "let" (Ls bnds) bod ->
     -- mkLets tacks on NoLoc's for every expression.
     -- Here, we remove the outermost NoLoc and tag with original src location
     (loc l . unLoc) <$> (mkLets <$> (mapM letbind bnds) <*> (exp bod))

   Ls3 _ "let*" (Ls []) bod -> exp bod

   Ls3 l "let*" (Ls (bnd:bnds)) bod -> do
     bnd'  <- letbind bnd
     bnds' <- exp $ Ls3 l "let*" (Ls bnds) bod
      -- just like the `let` case above
     pure $ loc l $ unLoc $ mkLets [bnd'] bnds'

   Ls (A l "case": scrut: cases) -> do
     e' <- CaseE <$> (exp scrut) <*> (mapM docase cases)
     pure $ loc l e'

   Ls (A l p : ls) | isPrim p -> loc l . PrimAppE (prim p) <$> mapM exp ls

   Ls (A l "lambda" : Ls args : [bod]) -> do
     -- POLICY DECISION:
     -- Should we require type annotations on the arguments to a lambda ?
     -- Right now, we don't and initialize them with meta type variables.
     let args' = L.map getSym args
     bod' <- exp bod
     tys <- mapM  (\_ -> newMetaTy) args'
     pure $ loc l $ Ext $ LambdaE (zip args' tys) bod'

   Ls3 l "for/list" (Ls1 (Ls4 _ v ":" t e)) bod -> do
     e'   <- exp e
     bod' <- exp bod
     pure $ loc l $ MapE (textToVar v, typ t, e') bod'

   -- I don't see why we need the extra type annotation:
   Ls4 l "for/fold"
          (Ls1 (Ls4 _ v1 ":" t1 e1))
          (Ls1 (Ls4 _ v2 ":" t2 e2))
          bod -> do
     e1'  <- exp e1
     e2'  <- exp e2
     bod' <- exp bod
     pure $ loc l $ FoldE (textToVar v1, typ t1, e1')
                          (textToVar v2, typ t2, e2')
                          bod'

   Ls3 l "vector-ref" evec (G _ (HSInt ind)) ->
       loc l . ProjE (fromIntegral ind) <$> (exp evec)

   Ls (A l "par" : es) -> loc l . Ext <$> ParE0 <$> mapM exp es

   Ls3 l "letarena" v e -> do
     e' <- exp e
     let v' = getSym v
     pure $ loc l $ WithArenaE v' e'

   Ls (A l "vector" : es) -> loc l . MkProdE <$> mapM exp es

   -- Dictionaries require type annotations for now.  No inference!
   Ls3 l "ann" (Ls2 _ "empty-dict" a) (Ls3 _ "SymDict" b ty) -> do
     a' <- exp a
     b' <- exp b
     unless (a' == b') $ error $ "Expected annotation on SymDict:" ++ show a'
     pure $ loc l $ PrimAppE (DictEmptyP $ typ ty) [a']

   Ls5 l "insert" a d k (Ls3 _ "ann" v ty) -> do
     a' <- exp a
     d' <- exp d
     k' <- exp k
     v' <- exp v
     pure $ loc l $ PrimAppE (DictInsertP $ typ ty) [a',d',k',v']

   Ls3 l "ann" (Ls3 _ "lookup" d k) ty -> do
     d' <- exp d
     k' <- exp k
     pure $ loc l $ PrimAppE (DictLookupP $ typ ty) [d', k']

   Ls3 l "ann" (Ls3  _ "has-key?" d k) ty -> do
     d' <- exp d
     k' <- exp k
     pure $ loc l $ PrimAppE (DictHasKeyP $ typ ty) [d', k']

   -- L [A "error",arg] ->
   Ls3 l "ann" (Ls2 _ "error" arg) ty ->
     case arg of
       G _ (HSString str) -> pure $ loc l $ PrimAppE (ErrorP (T.unpack str) (typ ty)) []
       _ -> error$ "bad argument to 'error' primitive: "++prnt arg

   -- Other annotations are dropped:
   Ls3 _ "ann" e _ty -> exp e

   Ls (A _ kwd : _args) | isKeyword kwd ->
      error $ "Error reading treelang. " ++ show kwd ++ "is a keyword:\n "++prnt se

   ----------------------------------------
   -- If NOTHING else matches, we are an application.  Be careful we didn't miss anything:
   Ls (A l rator : rands) ->
     let app = (loc l) . AppE (textToVar rator) []
     in app <$> mapM exp rands

   _ -> error $ "Expression form not handled (yet):\n  "++
               show se ++ "\nMore concisely:\n  "++ prnt se


-- | One case of a case expression
docase :: Sexp -> PassM (DataCon,[(Var,Ty0)], L Exp0)
docase s =
  case s of
    RSList [ RSList (A _ con : args)
           , rhs ]
      -> do args' <- mapM f args
            rhs'  <- exp rhs
            pure (textToDataCon con, args', rhs')
    _ -> error$ "bad clause in case expression\n  "++prnt s
 where
   f x  = (getSym x, ) <$> newMetaTy

letbind :: Sexp -> PassM (Var,[l],Ty0, L Exp0)
letbind s =
  case s of
   RSList [A _ vr, A _ ":", ty, rhs] ->
     (textToVar vr, [], typ ty, ) <$> exp rhs
   -- A let binding without a type annotation.
   RSList [A _ vr, rhs] ->
     (textToVar vr, [], , ) <$> newMetaTy <*> exp rhs
   _ -> error $ "Badly formed let binding:\n  "++prnt s

isPrim :: Text -> Bool
isPrim p = S.member p (M.keysSet primMap)

-- ^ A map between SExp-frontend prefix function names, and Gibbon
-- abstract Primops.
primMap :: M.Map Text (Prim d)
primMap = M.fromList
  [ ("+", AddP)
  , ("-", SubP)
  , ("*", MulP)
  , ("div", DivP)
  , ("mod", ModP)
  , ("exp", ExpP)
  , ("rand", RandP)
  , ("eqsym", EqSymP)
  , ("=", EqIntP)
  , ("<", LtP)
  , (">", GtP)
  , ("<=", LtEqP)
  , (">=", GtEqP)
  , ("or" , OrP)
  , ("and", AndP)
  , ("size-param", SizeParam)
  , ("sym-append", SymAppend)
  , ("True", MkTrue)
  , ("False", MkFalse)
  , ("gensym", Gensym)
  , ("printint", PrintInt)
  , ("printsym", PrintSym)
  , ("readint", ReadInt)
  , ("sym-set-empty", SymSetEmpty)
  , ("sym-set-insert", SymSetInsert)
  , ("sym-set-contains", SymSetContains)
  , ("sym-hash-empty", SymHashEmpty)
  , ("sym-hash-insert", SymHashInsert)
  , ("sym-hash-lookup", SymHashLookup)
  ]

prim :: Text -> Prim Ty0
prim t = case M.lookup t primMap of
           Just x -> x
           Nothing -> error$ "Internal error, this is not a primitive: "++show t


handleRequire :: FilePath -> [RichSExpr (SC.Located HaskLikeAtom)] ->
                 IO [RichSExpr (SC.Located HaskLikeAtom)]
handleRequire _ [] = return []
handleRequire baseFile (l:ls) =
  case l of
    (RSList [RSAtom (SC.At _ "require"), arg]) -> do
    -- (Ls2 "require" arg) -> do
       ls' <- handleRequire baseFile ls
       let file = case arg of
                    RSAtom (SC.At _ (HSString str)) -> (takeDirectory baseFile) </> (unpack str)
                    _ -> error $ "bad require line: " ++ (show arg)
       dbgPrintLn lvl $ "Including required file: "++show file
       txt <- fmap bracketHacks $ readFile file
       dbgPrintLn lvl $ "Parsing required text: "++show txt
       let res :: Either String [RichSExpr (SC.Located HaskLikeAtom)]
           res = fmap (fmap toRich) $
                 decode treelangParser txt
       case res of
         Left err -> error err
         -- Right ls -> return $ ls ++ ls'
         Right l' -> return $ l' ++ ls'
    _ -> do
      ls' <- handleRequire baseFile ls
      return $ l:ls'

-- ^ Parse a file to an L1 program.  Return also the gensym counter.
parseFile :: FilePath -> IO (PassM Prog0)
parseFile file = do
  txt    <- fmap bracketHacks $
            -- fmap stripHashLang $
            readFile file
  dbgPrintLn lvl $ "Parsing text: "++show txt
  let res :: Either String [RichSExpr (SC.Located HaskLikeAtom)]
      res = fmap (fmap toRich) $
            decode treelangParser txt
  dbgPrintLn lvl "Result of parsing:"
  case res of
     Left err -> error err
     Right ls -> do
       ls' <- handleRequire file ls
       return $ parseSExp ls'
