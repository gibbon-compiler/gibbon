module Main where

import Strings
import Contents
import Adts

-- This error occurs when you try to traverse the list make via the copy Packed call again. 
-- The loop function below gets the newAdt which has indirection and redirection tags but when it tries to 
-- re-run the processAdt function again it hits a null byte and exits with the messgage: "Unknown tag in: tmpval_6290"  
         
processAdt :: Adt -> Adt
processAdt adt = case adt of 
                    Nil -> Nil
                    AC rst content  -> let newContent = processContent content 
                                           newRst     = processAdt rst
                                       in AC newRst (copyPacked newContent)


loop :: Adt -> Int -> Adt 
loop adtIn iters = if (iters <= 0)
                   then adtIn
                   else let newAdt = processAdt adtIn
                        in loop newAdt (iters-1)                                 


gibbon_main = 
    let ac            = mkACList 80000 100
        ac_new        = iterate (loop ac 2)
    in ()
