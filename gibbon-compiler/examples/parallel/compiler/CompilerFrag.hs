module CompilerFrag where

import Compiler

bench_frag_seq_compiler :: ()
bench_frag_seq_compiler =
  let ex = make_big_ex sizeParam 0
      p = ProgramA (quote "Int") ex
      compiled = (compile2 p)
      n = iterate (countLeavesX86 compiled)
      _ = printint n
  in ()

bench_frag_par_compiler :: ()
bench_frag_par_compiler =
  let ex = make_big_ex sizeParam 0
      p = ProgramA (quote "Int") ex
      compiled_par = (compile2_par p)
      n = iterate (countLeavesX86 compiled_par)
      _ = printint n
  in ()


gibbon_main =
  if eqBenchProg "frag_seqcompiler"
  then bench_frag_seq_compiler
  else bench_frag_par_compiler
