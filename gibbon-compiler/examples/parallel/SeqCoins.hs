module SeqCoins where

data AList = ANil | ASing [Int] | Append AList AList

_copy_A :: AList -> AList
_copy_A tr =
    case tr of
        ANil     -> ANil
        ASing ls -> ASing ls
        Append l r ->
            let l' = _copy_A l
                r' = _copy_A r
            in Append l' r'

appendA :: AList -> AList -> AList
appendA l r =
    case l of
        ANil -> _copy_A r
        ASing xs ->
            case r of
                ANil         -> ASing xs
                ASing ys     -> Append (ASing xs) (ASing ys)
                Append ys zs -> Append (ASing xs) (Append (_copy_A ys) (_copy_A zs))
        Append xs ys ->
            case r of
                -- ANil         -> Append (_copy_A xs) (_copy_A ys)
                ASing zs     -> Append (Append (_copy_A xs) (_copy_A ys)) (ASing zs)
                Append zs as -> Append (Append (_copy_A xs) (_copy_A ys)) (Append (_copy_A zs) (_copy_A as))

depthA :: AList -> Int
depthA xs =
    case xs of
        ANil         -> 0
        ASing _      -> 1
        Append xs ys -> 1 + depthA xs + depthA ys

{-

payA :: Int -> [(Int,Int)] -> [Int] -> AList [Int]
payA 0   coins     acc = ASing acc
payA _   []        acc = ANil
payA val ((c,q):coins) acc
  | c > val   = payA val coins acc
  | otherwise = append left right -- strict in l, maybe strict in r
  where
    left  = payA (val - c) coins' (c:acc)
    right = payA val coins acc
    coins' | q == 1    = coins
           | otherwise = (c,q-1) : coins


-}

gibbon_main =
    let ls :: [Int]
        ls = vempty

        x = ANil
        y = ASing ls
        z = Append ANil (ASing ls)

        -- (ASing ls)
        a = appendA x y

        -- (ASing ls)
        b = appendA y x

        -- Append (ASing ls) (ASing ls)
        c = appendA a b

        d = appendA c c
    in depthA d
