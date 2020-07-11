module Coins where

import Gibbon.Vector

data AList = ANil | ASing Int | Append AList AList

lenA :: AList -> Int
lenA ls =
    case ls of
        ANil -> 0
        ASing i -> 1
        Append l r -> lenA l + lenA r

getCoins1 :: Int -> Int -> Vector (Int,Int) -> Vector (Int,Int)
getCoins1 c q coins_rst =
   let len = length coins_rst
   in if q == 1 then copy coins_rst else cons (c,q-1) coins_rst

printCoins :: Vector (Int, Int) -> Int
printCoins coins =
    let _ = printsym (quote "[")
        n = printCoins' 0 (length coins) coins
        _ = printsym (quote "]\n")
    in n

printCoins' :: Int -> Int -> Vector (Int, Int) -> Int
printCoins' start end coins =
    if start == end
    then 0
    else
        let tup = head coins
            _ = printCoin tup
            rst = tail coins
        in printCoins' (start+1) end rst

printCoin :: (Int, Int) -> Int
printCoin tup =
    let c = tup !!! 0
        q = tup !!! 1
        _ = printsym (quote "(")
        _ = printint c
        _ = printsym (quote ",")
        _ = printint q
        _ = printsym (quote "")
        _ = printsym (quote ")")
    in 0

payA_seq :: Int -> Vector (Int,Int) -> AList
payA_seq amt coins =
    if amt == 0
    then ASing 1
    else
        let len = length coins
        in if len == 0
        then ANil
        else
            let tup = head coins
                c = tup !!! 0
                q = tup !!! 1
                coins_rst = tail coins
            in if c > amt
            then payA_seq amt coins_rst
            else
                let coins1 = getCoins1 c q coins_rst
                    -- _ = printCoins coins
                    -- _ = printCoin tup
                    -- _ = printsym (quote "\n")
                    -- _ = printCoins coins1
                    left = payA_seq (amt - c) coins1
                    right = payA_seq amt coins_rst
                in Append left right

getDepth1 :: Int -> Int -> Int
getDepth1 q depth =
    if q == 1 then (depth-1) else depth

payA_par :: Int -> Int -> Vector (Int,Int) -> AList
payA_par depth amt coins =
    if depth == 0
    then payA_seq amt coins
    else if amt == 0
    then ASing 1
    else
        let len = length coins
        in if len == 0
        then ANil
        else
            let tup = head coins
                c = tup !!! 0
                q = tup !!! 1
                coins_rst = tail coins
            in if c > amt
            then payA_par depth amt coins_rst
            else
                let coins1 = getCoins1 c q coins_rst
                    depth1 = getDepth1 q depth
                    left = spawn (payA_par depth1 (amt - c) coins1)
                    right = payA_par (depth-1) amt coins_rst
                    _ = sync
                in Append left right
