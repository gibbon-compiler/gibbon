## LLVM Backend

The file `Monad.hs` implements the `CodeGen` state monad, which tracks the basic-blocks in a function, and the stack of instructions in each basic-block. This is mostly copied over from [AccelerateHS](https://github.com/AccelerateHS/accelerate-llvm/blob/master/accelerate-llvm/Data/Array/Accelerate/LLVM/CodeGen/Monad.hs), with only a few changes.

`Codegen.hs` contains functions to convert `Prog` to LLVM IR.


## Dependencies

* LLVM 5.0

* [llvm-hs](https://github.com/llvm-hs/llvm-hs)
