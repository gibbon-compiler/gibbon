import Movies

testInsert :: Int -> MovieTrie -> MovieTrie
testInsert i mt = if (i == 0) then mt 
                else 
                let 
                    title = getRandomString (mod rand 10)
                    movieContent = mkMovieContent title
                in testInsert (i-1) (insertMovie title Nothing movieContent mt)
gibbon_main = 
    let 
        mvt = iterate (testInsert 1000 Root)
    in ()