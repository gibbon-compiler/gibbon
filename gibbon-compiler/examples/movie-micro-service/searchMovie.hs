import Movies

type Text = Vector Char

getTitle :: Movie -> Text
getTitle m = case m of
    Empty -> " "
    Movie mt rd d w ci movietags rating -> mt

gibbon_main = 
    let
        movielist = genMovieList 100
        movie1 = fromMaybe " " (nth_plist movielist Nothing 10 )
        len1 = vlength movie1
        mt = consMovieTrie movielist Root
        mv = searchMovieTitle movie1 mt
        foundmovie = getTitle mv
        len2 = vlength foundmovie
    in len1 ==len2
