module Main where

import Strings
import Contents
import Adts


-- This program is for re-creating the copy packed bug. 
-- processAdtCorrect genertes the correct file, but to do so we have to insert a copyPacked call at the front end which the compiler should ideally do automatically. 
-- processAdtInCorrect is the same function but without the call to copyPacked. 
-- The Adt is printed after every function call.
-- Compilation command used: gibbon --packed  --no-gc --to-exe replicate_copyPacked_bug.hs
-- TODO: Paste C code to show what exactly is happening here. 
         
processAdtCorrect :: Adt -> Adt
processAdtCorrect adt = case adt of 
				Nil -> Nil
				AC rst content  -> let newContent = processContent content 
						       newRst     = processAdtCorrect rst
                                                   in AC newRst (copyPacked newContent)

processAdtInCorrect :: Adt -> Adt
processAdtInCorrect adt = case adt of
				Nil -> Nil
                                AC rst content  -> let newContent = processContent content
                                                       newRst     = processAdtCorrect rst
                                                   in AC newRst newContent


gibbon_main = 
    let ac            = mkACList 3 5
        _             = printsym (quote "Printing the AC Adt right after constructing it\n")
        _             = printPacked ac
        _             = printsym (quote "NEWLINE")
        ac_correct    = processAdtCorrect ac
        _             = printsym (quote "Print the new Adt after calling processAdtCorrect function\n")
        _             = printPacked ac_correct
        _             = printsym (quote "NEWLINE")
        ac_incorrect  = processAdtInCorrect ac
        _             = printsym (quote "Printing the new Adt after calling processAdtInCorrect function\n")
        _             = printPacked ac_incorrect
        _             = printsym (quote "NEWLINE")
    in ()
