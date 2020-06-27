module T127c where

data List a = Nil | Cons a (List a)

data Maybe a = Nothing | Just a

mbInts :: Maybe (List Int)
mbInts = Just Nil

gibbon_main = let x = mbInts in 10
