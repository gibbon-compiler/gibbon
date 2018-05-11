module Gibbon.Passes.LLVM.Type where

import qualified LLVM.AST as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Type as T

class TypeOf x where
  typeOf :: x -> T.Type

instance TypeOf AST.Operand where
  typeOf op =
    case op of
      (AST.LocalReference ty _) -> ty
      (AST.ConstantOperand c)   -> typeOf c
      _ -> error $ "typeOf Op: Not implemented " ++ show op

instance TypeOf C.Constant where
  typeOf c =
    case c of
      (C.Int bits _) -> T.IntegerType bits
      _ -> error $ "typeOf Constant: Not implemented " ++ show c

data KindOf = IntegerK | PointerK | NamedK

kindOf :: T.Type -> KindOf
kindOf (T.IntegerType _) = IntegerK
kindOf (T.PointerType _ _) = PointerK
kindOf (T.NamedTypeReference (AST.Name _)) = NamedK
kindOf oth = error $ "kindOf: Unexpected " ++ show oth
