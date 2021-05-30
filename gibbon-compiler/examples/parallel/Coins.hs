{-# LANGUAGE NoImplicitPrelude #-}

module Coins where

import Gibbon.Prelude

--------------------------------------------------------------------------------

data AList = ANil Int | ASing Int | Append AList AList

lenA :: AList -> Int
lenA ls =
    case ls of
        ANil i -> 0
        ASing i -> 1
        Append l r -> lenA l + lenA r

type CoinQty = ( Int -- value
               , Int -- quantity
               )

getCoins1 :: Int -> Int -> List CoinQty -> List CoinQty
{-# INLINE getCoins1 #-}
getCoins1 c q coins_rst =
   if q == 1 then copy_ll coins_rst else cons_ll (c,q-1) coins_rst

-- printCoins :: List CoinQty -> ()
-- printCoins coins =
--     let _ = printVec (\tup -> printCoin tup) coins
--         _ = printsym (quote "\n")
--     in ()

printCoin :: CoinQty -> ()
printCoin tup =
    let (a,b) = tup
        _ = printsym (quote "(")
        _ = printint a
        _ = printsym (quote ",")
        _ = printint b
        _ = printsym (quote ")")
    in ()

payA_seq :: Int -> List CoinQty -> AList
payA_seq amt coins =
    if amt == 0
    then ASing 1
    else
        if is_empty_ll coins
        then ANil 0
        else
            let (c,q) = head_ll coins
                coins_rst = tail_ll coins
            in if c > amt
            then payA_seq amt coins_rst
            else
                let coins1 = getCoins1 c q coins_rst
                    left = payA_seq (amt - c) coins1
                    right = payA_seq amt coins_rst
                    _ = free_ll coins1
                    -- _ = vfree coins1
                    -- _ = vfree2 coins_rst
                in Append left right

getDepth1 :: Int -> Int -> Int
getDepth1 q depth =
    if q == 1 then (depth-1) else depth

payA_par :: Int -> Int -> List CoinQty -> AList
payA_par depth amt coins =
    if depth == 0
    then payA_seq amt coins
    else if amt == 0
    then ASing 1
    else
        if is_empty_ll coins
        then ANil 0
        else
            let (c,q) = head_ll coins
                coins_rst = tail_ll coins
            in if c > amt
            then payA_par depth amt coins_rst
            else
                let coins1 = getCoins1 c q coins_rst
                    depth1 = getDepth1 q depth
                    left = spawn (payA_par depth1 (amt - c) coins1)
                    right = payA_par (depth-1) amt coins_rst
                    _ = sync
                    _ = free_ll coins1
                    -- _ = vfree2 coins_rst
                in Append left right

payA_par_nograin :: Int -> List CoinQty -> AList
payA_par_nograin amt coins =
    -- if depth == 0
    -- then payA_seq amt coins
    -- else
    if amt == 0
    then ASing 1
    else
        if is_empty_ll coins
        then ANil 0
        else
            let (c,q) = head_ll coins
                coins_rst = tail_ll coins
            in if c > amt
            then payA_par_nograin amt coins_rst
            else
                let coins1 = getCoins1 c q coins_rst
                    -- depth1 = getDepth1 q depth
                    left = spawn (payA_par_nograin (amt - c) coins1)
                    right = payA_par_nograin amt coins_rst
                    _ = sync
                    _ = free_ll coins1
                    -- _ = vfree2 coins_rst
                in Append left right


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
    let coins0 :: List (Int,Int)
        coins0 = alloc_ll
        coins1 = cons_ll (250,55) coins0
        coins2 = cons_ll (100,88) coins1
        coins3 = cons_ll (25,88) coins2
        coins4 = cons_ll (10,99) coins3
        coins5 = cons_ll (5,122) coins4
        coins6 = cons_ll (1,177) coins5
        amt = sizeParam
        tr = iterate (payA_seq amt coins6)
    -- in check_coins amt tr
    in ()
