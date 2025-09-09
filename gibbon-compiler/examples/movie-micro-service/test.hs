import Movies
-- data Ttext = Ttext (Vector Char)
printMovieTrie :: MovieTrie -> ()
printMovieTrie mt = case mt of
                        Root -> printsym (quote "nothing")
                        MovieTrie ch ismovie movie lmt -> if (isNothing ch) then 
                                                                        let 
                                                                        _ = printsym (quote "/")
                                                                        in if (isNothing lmt) then ()
                                                                        else print_MThelper (fromMaybe Nil lmt)
                                    else let
                                        a = fromMaybe ' ' ch
                                        _ = printchar a
                                        in if (isNothing lmt) then ()
                                        else print_MThelper (fromMaybe Nil lmt)
print_MThelper :: (PList MovieTrie)->()
print_MThelper lmt = case lmt of 
    Nil -> ()
    Cons x xs -> case x of 
        Root -> print_MThelper xs 
        MovieTrie ch ismovie movie lmt -> let 
                                        _ = printchar (fromMaybe ' ' ch)
                                        _ = print_MThelper (fromMaybe Nil lmt)
                                        in print_MThelper xs

gibbon_main =
    -- let 
    -- -- testMovie = Movie 'a' "MovieTitle" "ReleaseDate"
    -- -- testMovie = Empty
    -- ttext = Ttext "fsaf"
    -- -- testMovieTrie = MovieTrie (Just testMovie) (Just "Word") (Nothing)
    -- -- testMovieTrie = MovieTrie testMovie
    -- -- _ = printPacked testMovie
    
    -- _ = printsym (quote "NEWLINE")
    -- _ = printPacked ttext
    -- -- _ = printsym (quote "NEWLINE")
    -- in ()
    -- putStrLn getRandomString 13
    let 
        ri = mod rand 10
        ri2 = mod rand 10
        _ = printint ri2
        _ = printint ri
        -- smovie = mkMovieContent "titan"
        -- movieT = insertMovie "titan" Nothing smovie Root 
        -- _ = printsym (quote " ")
        -- _ = printMovieTrie movieT
        -- movieT = insertMovie "titen" Nothing smovie movieT
        -- _ = printsym (quote " ")
        -- _ = printMovieTrie movieT
        -- _ = printsym (quote "test")
        -- mc = iterate (searchMovieTitle "tit" movieT)
        -- movieT = deleteMovie "titan" movieT 
        -- _ = printsym (quote " ")
        -- _ = printMovieTrie movieT

        -- _ = printPacked mc
        -- _ = printPacked movieT
        -- let 
        --     _ = case movieT of
        --         Empty -> printsym (quote "empty")
        --         MovieTrie _ _ _ _ _ _ ->printsym (quote "valid")
        -- in (
        -- _ = printMovieTrie movieT
        -- _ = if isEmptyM mc then printsym(quote "notfound") else printsym (quote "found")
        -- _ = printPacked
        -- _ = printsym (quote "a")
    in ()
