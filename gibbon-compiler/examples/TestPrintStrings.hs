module TestPrintStrings where

import Gibbon.Vector

gibbon_main = 
   let str :: Vector Char 
       str = "Success Printing a String to Stdout works in Gibbon!"
       _   = printVec (\i -> printchar i) str
   in ()
