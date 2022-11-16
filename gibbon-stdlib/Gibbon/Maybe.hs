{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Gibbon.Maybe where

import Gibbon.Prelude
import Gibbon.Prim

-----------------------------------------------------------

data Maybe a = Just a | Nothing



isJust :: Maybe a -> Bool 
isJust val = case val of 
		Nothing -> False 
		Just a  -> True


isNothing :: Maybe a -> Bool 
isNothing val = case val of 
		  Nothing -> True 
		  Just a  -> False 


fromJust :: Maybe Int -> Int 
fromJust val = case val of 
		Nothing -> (error "Maybe fromJust Nothing" :: Int) 
  		Just x  -> x

fromMaybe :: a -> Maybe a -> a 
fromMaybe d x = case x of 
		   Nothing -> d 
		   Just v  -> v


