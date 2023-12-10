module Main where

import Strings
import Contents
import Adts
import Tags

-- Trigger the bug in the calculate bounds pass. 
-- Error message: 
-- recovertype/primapp: MkTrue []
-- recovertype/primapp: MkFalse []
-- gibbon: Map lookup failed on key: Var "cpy_3273" in map:
-- []
-- CallStack (from HasCallStack):
--  error, called at src/Gibbon/Common.hs:289:7 in gibbon-0.2-inplace:Gibbon.Common
--  err, called at src/Gibbon/Common.hs:302:22 in gibbon-0.2-inplace:Gibbon.Common
--  #, called at src/Gibbon/Passes/CalculateBounds.hs:174:110 in gibbon-0.2-inplace:Gibbon.Passes.CalculateBounds
--  current work around is commenting out the this line  else go "inferRegSize" inferRegSize l2 in Compiler.hs pass and replacing it with pure l2
--  compiled via: gibbon --packed --no-gc --to-exe replicate_calculateBounds_bug.hs

searchTagAdt :: Adt -> Tags -> Adt
searchTagAdt inList tag = case inList of
				Nil -> Nil
                                TCA tags content rst -> let present = searchTag tag tags
                                                            newRst  = searchTagAdt rst tag
                                                        in if (present) then TCA tags content newRst else newRst
                                TAC tags rst content -> let present = searchTag tag tags
                                                            newRst  = searchTagAdt rst tag
                                                        in if (present) then TAC tags newRst content else newRst
                                ACT rst content tags -> let present = searchTag tag tags
				                 	    newRst  = searchTagAdt rst tag
                                                        in if (present) then ACT newRst content tags else newRst
                                ATC rst tags content -> let present = searchTag tag tags
                                                            newRst  = searchTagAdt rst tag
                                                        in if (present) then ATC newRst tags content else newRst


-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let act = mkACTList 100000 50 1000 
        tag = Tag 1000000 Nul        
        add_act    = iterate (searchTagAdt act tag)
    in ()
