module Gibbon.Passes.LLVM.Terminator where

-- |
-- Copyright   : [2015] Trevor L. McDonell
-- License     : BSD3
--

-- | standard library
import Control.Monad.State
import qualified Data.Sequence as Seq

-- | llvm-hs
import qualified LLVM.AST as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Instruction as I
import Gibbon.Passes.LLVM.Monad


-- | Add a termination condition to the current instruction stream. Also return
-- the block that was just terminated.
--
terminate :: AST.Terminator -> CodeGen BlockState
terminate term =
  state $ \s ->
    case Seq.viewr (blockChain s) of
      Seq.EmptyR  -> error $ "terminate empty block chain " ++ show s
      bs Seq.:> b -> ( b, s { blockChain = bs Seq.|> b { terminator = Just term } } )


-- | Return a value from a basic block
--
retval' :: AST.Operand -> CodeGen BlockState
retval' x = terminate $ AST.Ret (Just x) []

-- | Return void from a basic block
--
return' :: CodeGen BlockState
return' = terminate $ AST.Ret Nothing []


-- | Unconditional branch. Return the name of the block that was branched from.
--
br :: BlockState -> CodeGen BlockState
br target = terminate $ AST.Br (blockLabel target) []


-- | Conditional branch. Return the name of the block that was branched from.
--
cbr :: AST.Operand -> BlockState -> BlockState -> CodeGen BlockState
cbr cond t f = terminate $ I.CondBr cond (blockLabel t) (blockLabel f) []


-- | Transfer control flow to one of several different places
--
switch :: AST.Operand -> AST.Name -> [(C.Constant, AST.Name)] -> CodeGen BlockState
switch cmp defaultDest dests = terminate $ I.Switch cmp defaultDest dests []
