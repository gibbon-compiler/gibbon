module T127c where

data MyList a = Nil | Cons a (MyList a)

data Maybe a = Nothing | Just a

mbInts :: Maybe (MyList Int)
mbInts = Just Nil

gibbon_main = let x = mbInts in 10
