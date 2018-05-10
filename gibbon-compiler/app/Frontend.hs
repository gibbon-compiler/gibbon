module Main where
import System.Environment (getArgs)
import Gibbon.Compiler (compileCmd)

main :: IO ()
main = getArgs >>= compileCmd 
