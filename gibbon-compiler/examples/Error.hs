f :: Int -> Int
f x = if (x == 1) then 42 else (error "error" :: Int)

gibbon_main =
    f 1

main = print $ f 1
