import Movies

type Text = Vector Char

getTitle :: Movie -> Text
getTitle m = case m of
    Empty -> " "
    Movie mt rd d w ci movietags rating -> mt

gibbon_main = 
    let
        movielist = genMovieList 1000
        movie1 = fromMaybe " " (nth_plist movielist Nothing 100)
        mt = consMovieTrie movielist Root
        mv = iterate (searchMovieTitle movie1 mt)
    in ()
