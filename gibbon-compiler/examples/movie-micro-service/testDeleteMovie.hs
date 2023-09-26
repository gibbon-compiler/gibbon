import Movies 

type Text = Vector Char

testDelete :: (PList Text) -> MovieTrie -> MovieTrie 
testDelete lt mt = 
    case lt of 
        Nil -> Root
        Cons x xs -> testDelete xs (deleteMovie x mt)

gibbon_main = 
    let 
        movielist  = genMovieList 20
        mt = consMovieTrie movielist Root 
        mt2 = iterate (testDelete movielist mt)
    in ()