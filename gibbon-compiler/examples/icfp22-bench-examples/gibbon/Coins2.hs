{-# LANGUAGE NoImplicitPrelude #-}

module Coins where

import Gibbon.Prelude

--------------------------------------------------------------------------------

data AList = ANil Int | ASing Int | Append AList AList

data PList a = Cons a (PList a) | Nil

lenA :: AList -> Int
lenA ls =
    case ls of
        ANil i -> 0
        ASing i -> 1
        Append l r -> lenA l + lenA r

type CoinQty = ( Int -- value
               , Int -- quantity
               )

isEmpty :: PList a -> Bool
isEmpty ls =
  case ls of
    Nil -> True
    Cons _ _ -> False


head :: PList a -> a
head ls =
  case ls of
    Cons x xs -> x

tail :: PList a -> PList a
tail ls =
  case ls of
    Cons x xs -> xs

getCoins1 :: Int -> Int -> PList CoinQty -> PList CoinQty
-- {-# INLINE getCoins1 #-}
getCoins1 c q coins_rst =
   if q == 1 then coins_rst else Cons (c,q-1) coins_rst

payA_seq :: Int -> PList CoinQty -> AList
payA_seq amt coins =
    if amt == 0
    then ASing 1
    else
        -- if isEmpty coins
        -- then ANil 0
        -- else
            case coins of
              Nil -> ANil 0
              Cons hd coins_rst ->
                let (c,q) = hd
                in if c > amt
                then payA_seq amt coins_rst
                else
                  if q == 1
                  then let left = payA_seq (amt - c) coins_rst
                           right = payA_seq amt coins_rst
                       in Append left right
                  else let coins1 = Cons (c,q-1) coins_rst
                           left = payA_seq (amt - c) coins1
                           right = payA_seq amt coins_rst
                       in Append left right


getDepth1 :: Int -> Int -> Int
getDepth1 q depth =
    if q == 1 then (depth-1) else depth

check_coins :: Int -> AList -> ()
check_coins amt tr =
    let n = lenA tr in
    if amt == 777
    then print_check (n == 140899)
    else if amt == 999
    then print_check (n == 329565)
    -- assume its correct
    else
        let _ = printint n
            _ = printsym (quote "\n")
        in print_check True

gibbon_main =
    let coins0 :: PList (Int,Int)
        -- coins0 = alloc_ll
        -- coins1 = cons_ll (250,55) coins0
        -- coins2 = cons_ll (100,88) coins1
        -- coins3 = cons_ll (25,88) coins2
        -- coins4 = cons_ll (10,99) coins3
        -- coins5 = cons_ll (5,122) coins4
        -- coins6 = cons_ll (1,177) coins5
        coins6 = Cons (1,177) (Cons (5,122) (Cons (10,99) (Cons (25,88) (Cons (100,88) (Cons (250,55) Nil)))))
        amt = sizeParam
        tr = iterate (payA_seq amt coins6)
    in check_coins amt tr
    -- in ()
