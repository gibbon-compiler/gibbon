module Main where

import Strings
import Contents
import Adts                             

-- When running the code, it segfaults in the free_region function. 
-- Compile command -> gibbon --packed --to-exe replicate_failing_gc.hs
--
-- GDB Backtrace
-- Program received signal SIGSEGV, Segmentation fault.
-- free_region (end_reg=end_reg@entry=0x555555562550 "\260 VUUU") at replicate_failing_gc.c:1011
-- 1011	            next_chunk = (char*) next_chunk_footer->rf_next;
-- (gdb) bt
-- #0  free_region (end_reg=end_reg@entry=0x555555562550 "\260 VUUU") at replicate_failing_gc.c:1011
-- #1  0x000055555555b79a in __main_expr () at replicate_failing_gc.c:4371
-- #2  0x00005555555554f4 in main (argc=1, argv=0x7fffffffdde8) at replicate_failing_gc.c:1443

getLength :: Adt -> Int
getLength adt = case adt of 
                     Nil              -> 0
                     AC next content  -> 1 + getLength next

                            
gibbon_main = 
    let ac = mkACList 1000 100
        count1 = iterate (getLength ac)
    in ()
