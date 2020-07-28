module Coins where

import Gibbon.Vector
import Gibbon.Vector.Parallel

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

printCoins :: Vector (Int, Int) -> ()
printCoins coins =
    let _ = printVec (\tup -> printCoin tup) coins
        _ = printsym (quote "\n")
    in ()

printCoin :: (Int, Int) -> ()
printCoin tup =
    let a = tup !!! 0
        b = tup !!! 1
        _ = printsym (quote "(")
        _ = printint a
        _ = printsym (quote ",")
        _ = printint b
        _ = printsym (quote ")")
    in ()

payA_seq :: Int -> Vector (Int,Int) -> AList
payA_seq amt coins =
    if amt == 0
    then ASing 1
    else
        let len = length coins
        in if len == 0
        then ANil
        else
            let (c,q) = head coins
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
                    _ = vfree coins1
                    _ = vfree2 coins_rst
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
            let (c,q) = head coins
                coins_rst = tail coins
            in if c > amt
            then payA_par depth amt coins_rst
            else
                let coins1 = getCoins1 c q coins_rst
                    depth1 = getDepth1 q depth
                    left = spawn (payA_par depth1 (amt - c) coins1)
                    right = payA_par (depth-1) amt coins_rst
                    _ = sync
                    _ = vfree coins1
                    _ = vfree2 coins_rst
                in Append left right
