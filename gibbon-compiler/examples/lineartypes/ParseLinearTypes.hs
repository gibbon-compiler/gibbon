{-# LANGUAGE LinearTypes #-}

module ParseLinearTypes where

{- This test should fail when --ghc-tc is passed to Gibbon
   because linearId is not linear like its type says. -}
linearId :: Int %1-> Int
linearId x = 123
