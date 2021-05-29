module CompilerFrag where

import Compiler

bench_frag_seq_compiler :: ()
bench_frag_seq_compiler =
  let ex = make_big_ex 15 0
      p = ProgramA (quote "Int") ex
      compiled = (compile2 p)
      n = iterate (countLeavesX86 compiled)
      _ = printint n
  in ()

bench_frag_par_compiler :: ()
bench_frag_par_compiler =
  let ex = make_big_ex 15 0
      p = ProgramA (quote "Int") ex
      compiled_par = (compile2_par p)
      n = iterate (countLeavesX86 compiled_par)
      _ = printint n
  in ()

loop_trav_compiler :: Int -> PseudoX86 -> Int
loop_trav_compiler iter tr =
    let n = countLeavesX86 tr
    in if iter == 1
       then n
       else loop_trav_compiler (iter-1) tr

bench_frag_seq_compiler_loop :: ()
bench_frag_seq_compiler_loop =
  let ex = make_big_ex 15 0
      p = ProgramA (quote "Int") ex
      compiled = (compile2 p)
      iters = sizeParam
      _ = printsym (quote "running ")
      _ = printint iters
      _ = printsym (quote " times.\n")
      n = iterate (loop_trav_compiler iters compiled)
      _ = printint n
  in ()

bench_frag_par_compiler_loop :: ()
bench_frag_par_compiler_loop =
  let ex = make_big_ex 15 0
      p = ProgramA (quote "Int") ex
      compiled_par = (compile2_par p)
      iters = sizeParam
      _ = printsym (quote "running ")
      _ = printint iters
      _ = printsym (quote " times.\n")
      n = iterate (loop_trav_compiler iters compiled_par)
      _ = printint n
  in ()


gibbon_main =
  if eqBenchProg "frag_seqcompiler"
  then bench_frag_seq_compiler
  else if eqBenchProg "frag_parcompiler"
  then bench_frag_par_compiler
  else if eqBenchProg "frag_seqcompiler_loop"
  then bench_frag_seq_compiler_loop
  else if eqBenchProg "frag_parcompiler_loop"
  then bench_frag_par_compiler_loop
  else ()
