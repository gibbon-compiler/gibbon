{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Gibbon.Passes.LLVM.Gibbon (
    addp, subp, mulp, eqp, callp
  , sizeParam, typeOf, printString, toIfPred
  , readTag, readInt, writeTag, writeInt, newBuf
  , sizeof, convert
  , addStructs, structName, populateStruct, unpackPtrStruct
) where

-- | standard library
import Data.ByteString.Short
import Data.Word (Word64)
import Control.Monad.State

-- | gibbon internals
import Gibbon.L4.Syntax
import Gibbon.Passes.Codegen (harvestStructTys, makeName)
import Gibbon.Common (fromVar)
import Gibbon.Passes.LLVM.Monad
import Gibbon.Passes.LLVM.Instruction
import Gibbon.Passes.LLVM.Terminator
import Gibbon.Passes.LLVM.Type
import Gibbon.Passes.LLVM.Utils
import qualified Gibbon.Passes.LLVM.Global as LG

-- | llvm-hs
import qualified LLVM.AST as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Type as T
import qualified LLVM.AST.Global as G

-- | Allow results of LLVM operations to be assigned to variables, instead of unnames
--

gibbonOp :: (InstrRet -> [AST.Operand] -> CodeGen AST.Operand)
            -> [(Var,Ty)] -> [AST.Operand]
            -> CodeGen BlockState
gibbonOp op bnds args =
  case bnds of
    [] -> op FreshVar args >>= retval'
    [(v, _)] -> do
      let nm = fromVar v
      res   <- op (NamedVar $ toByteString nm) args
      retval' res
    _ -> do
      struct <- op FreshVar args
      unpackValStruct FreshVar struct bnds


addp :: [(Var, Ty)] -> [AST.Operand] -> CodeGen BlockState
addp = gibbonOp add

mulp :: [(Var, Ty)] -> [AST.Operand] -> CodeGen BlockState
mulp = gibbonOp mul

subp :: [(Var, Ty)] -> [AST.Operand] -> CodeGen BlockState
subp = gibbonOp sub

eqp :: [(Var, Ty)] -> [AST.Operand] -> CodeGen BlockState
eqp  = gibbonOp eq

callp :: G.Global -> [(Var, Ty)] -> [AST.Operand] -> CodeGen BlockState
callp fn = gibbonOp (call fn)


-- | Gibbon SizeParam primitive
--
sizeParam :: [(Var,Ty)] -> CodeGen BlockState
sizeParam [(v,ty)] = do
  let nm = fromVar v
  _     <- load (toPtrTy lty) (NamedVar $ toByteString nm) op
  return'
  where lty = typeOf ty
        op  = globalOp (toPtrTy lty) (AST.Name $ toByteString "global_size_param")


-- | Convert Gibbon types to LLVM types.
--
-- Should be defined in Type.hs. But this would be right place to
-- define it, if we ever convert this into an independent library
-- as an abstraction over llvm-general
--
instance TypeOf Ty where
  typeOf IntTy       = T.i64                 -- ^ long long
  typeOf TagTyPacked = T.i8                  -- ^ char
  typeOf TagTyBoxed  = typeOf IntTy          -- ^ long long
  typeOf SymTy       = T.i64                 -- ^ long long
  typeOf PtrTy       = toPtrTy T.i8          -- ^ char*
  typeOf CursorTy    = toPtrTy T.i8          -- ^ char*
  typeOf (ProdTy []) = T.VoidType            -- ^ void (pointers to void are invalid in LLVM)
  typeOf (ProdTy ts) = typeOf ts
  typeOf (SymDictTy _t) = toPtrTy $ T.NamedTypeReference $ AST.Name $ toByteString "struct.dict_item"

-- | struct types
instance TypeOf [Ty] where
  typeOf = T.NamedTypeReference . AST.Name . toByteString . structName


-- | Gibbon PrintString
--
printString :: String -> CodeGen BlockState
printString s = do
  var <- allocate ty FreshVar
  _   <- store var chars
  nm  <- gets next
  -- TODO(cskksc): figure out the -1. its probably because store doesn't assign
  -- anything to an unname
  _   <- getElemPtr True (localRef (toPtrTy ty) (AST.UnName (nm - 1))) idxs
  _   <- call LG.fputs Void [localRef (toPtrTy T.i8) (AST.UnName nm)]
  return'
    where (chars, len) = stringToChar s
          ty    = T.ArrayType len T.i8
          idx   = (constop' . int') 0
          idxs  = [idx, idx]


-- | Convert string to a char array in LLVM format
--
stringToChar :: String -> (AST.Operand, Word64)
stringToChar s = (constop' $ string' s', len)
  where len = (fromIntegral . Prelude.length) s'
        s'  = s ++ ['\NUL']

-- | Generate the correct LLVM predicate
--
-- We implement the C notion of true/false i.e every value !=0 is truthy
--
toIfPred :: Triv -> CodeGen AST.Operand
toIfPred trv =
  case trv of
    (IntTriv i) -> do
      let op0 = (constop' . int' . toInteger) i
      notZeroP FreshVar op0
    (VarTriv v) -> do
      v' <- getvar (toByteString $ fromVar v)
      notZeroP FreshVar v'

-- | Read one byte from the cursor and advance it
--
-- TagTyPacked tagV = *(IntTy/TagTyPacked *) cur;
-- CursorTy curV = cur + 1;
--
readTag :: [(Var,Ty)] -> [AST.Operand] -> CodeGen BlockState
readTag [(tagV,TagTyPacked),(curV,CursorTy)] [cur] =
  readCursor [(tagV, TagTyPacked),(curV, CursorTy)] cur 1


-- | Read an 8 byte Int from the cursor and advance
--
-- (IntTy/TagTyPacked) valV = *(IntTy/TagTyPacked *) cur
-- CursorTy curV = cur + sizeof(IntTy)
--
readInt :: [(Var,Ty)] -> [AST.Operand] -> CodeGen BlockState
readInt [(valV,valTy),(curV,CursorTy)] [cur] =
  readCursor [(valV,valTy), (curV,CursorTy)] cur 8


readCursor :: [(Var, Ty)] -> AST.Operand -> Integer -> CodeGen BlockState
readCursor [(valV', valTy'), (curV', curTy')] cur' offset =
  let valTy = typeOf valTy'
      valV = fromVar valV'
      curTy = typeOf curTy'
      curV = fromVar curV'
  in do
    cur <- assign curTy FreshVar cur'

    -- valTy valV = *cur
    valVV <- load valTy FreshVar cur >>= convert valTy  FreshVar
    _ <- assign valTy (NamedVar $ toByteString valV) valVV

    -- curTy curV = cur + offset;
    curVV <- getElemPtr True cur [constop' $ int' offset]
    _ <- assign curTy (NamedVar $ toByteString curV) curVV
    return'

-- | Write a tag to the cursor, and advance it by 1
--
-- *cur = tag;
-- CursorTy outV = cur + 1;
--
writeTag :: [(Var,Ty)] -> [AST.Operand] -> CodeGen BlockState
writeTag [(outV, CursorTy)] [tag, cur] = do
  _ <- call LG.gwriteTag (NamedVar $ toByteString $ fromVar outV) [cur, tag]
  return'

writeInt ::  [(Var,Ty)] -> [AST.Operand] -> CodeGen BlockState
writeInt [(outV, CursorTy)] [val, cur] = do
  _ <- call LG.gwriteInt (NamedVar $ toByteString $ fromVar outV) [cur, val]
  return'


-- | Call malloc
newBuf :: [(Var,Ty)] -> [AST.Operand] -> CodeGen BlockState
newBuf [(outV, CursorTy)] [] = do
  let op = globalOp (toPtrTy T.i64) (AST.Name $ toByteString "global_size_param")
  bufSize <- load (toPtrTy T.i64) FreshVar op
  _ <- call LG.malloc (NamedVar $ toByteString $ fromVar outV) [bufSize]
  return'


-- | Generate instructions to convert op from type-of-op -> toTy
--
convert :: T.Type -> InstrRet -> AST.Operand -> CodeGen AST.Operand
convert toTy nm op =
  case (kindOf fromTy, kindOf toTy) of
    (IntegerK, IntegerK) -> sext toTy nm op
    (IntegerK, PointerK) -> inttoptr toTy nm op
    _                    -> bitcast toTy nm op
  where fromTy = typeOf op

-- |
sizeof :: T.Type -> CodeGen AST.Operand
sizeof ty = getElemPtr True (constop' $ C.Null ty) [constop' $ int' 1] >>= ptrToInt FreshVar


-- | Add all required structs
--
addStructs :: Prog -> CodeGen ()
addStructs prog = mapM_ (uncurry addTypeDef . defineStruct) $
                  harvestStructTys prog


-- | Generate LLVM type definitions (structs)
--
defineStruct :: [Ty] -> (ShortByteString, AST.Definition)
defineStruct [] = __
defineStruct tys = (nm', AST.TypeDefinition (AST.Name nm') (Just $ T.StructureType False elememtTypes))
  where nm = structName tys
        nm' = toByteString nm
        elememtTypes = map typeOf tys


-- | Return a reference to the struct, with its fields assigned to triv's
--
populateStruct :: T.Type -> InstrRet -> [AST.Operand] -> CodeGen AST.Operand
populateStruct ty nm ts = do
  struct <- allocate ty nm
  forM_ (zip ts [0..]) $ \(triv,i) -> do
    -- When indexing into a (optionally packed) structure, only i32 integer
    -- constants are allowed
    field <- getElemPtr True struct [constop' $ int32' 0, constop' $ int32' i]
    store field triv
  return struct


-- | Unpack elements of a struct from a var pointing to that struct
--
-- IntTy tag3 = ((Int64Int64Int64Prod *) fltCse2)->field0;
-- IntTy x0 = ((Int64Int64Int64Prod *) fltCse2)->field1;
unpackPtrStruct :: InstrRet -> AST.Operand -> [(Var, Ty)] -> CodeGen AST.Operand
unpackPtrStruct _nm struct bnds = do
  structTy <- case bnds of
                [] -> return $ typeOf struct
                _  -> return $ typeOf $ map snd bnds
  struct' <- convert (toPtrTy structTy) FreshVar struct
  forM_ (zip bnds [0..]) $ \((v,vty), i) -> do
    field <- getElemPtr True struct' [constop' $ int32' 0, constop' $ int32' i]
    field' <- load (typeOf vty) FreshVar field
    assign (typeOf vty) (NamedVar $ toByteString $ fromVar v) field'
  return struct'


-- | Unpack elements of a struct
--
-- PtrTy ptr5 = tmp_struct0.field0;
-- CursorTy tail6 = tmp_struct0.field1;
unpackValStruct :: InstrRet -> AST.Operand -> [(Var, Ty)] -> CodeGen BlockState
unpackValStruct nm struct bnds = do
  -- structTy <- case bnds of
  --               [] -> return $ typeOf struct
  --               _  -> return $ typeOf $ map snd bnds
  forM_ (zip bnds [0..]) $ \((v,vty), i) -> do
    extractValue nm struct [i] >>= assign (typeOf vty) (NamedVar $ toByteString $ fromVar v)
  return'

-- |
structName :: [Ty] -> String
structName tys = "struct." ++ makeName tys
