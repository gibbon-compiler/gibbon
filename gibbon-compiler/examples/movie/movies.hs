module Movies where
-- import Data.Map
import Gibbon.Prelude
import Gibbon.PList
import Gibbon.Vector
import Gibbon.Maybe
import Basics
-- ​
type Text = Vector Char 
-- ​
type IsMovie = Bool
type MovieTitle = Text 
type ReleaseDate = Text  
type Director =  Text 
type Writers = PList Text 
type CastInfo = PList Text
type MovieTags =  PList Text
type Rating = Int

-- --if IsMovie == True, the maybe values will exist
data Movie =    Empty
            |   Movie MovieTitle 
                ReleaseDate Director Writers CastInfo 
                MovieTags Rating 

data MovieTrie = Root
            |   MovieTrie (Maybe Char) (Maybe IsMovie) (Maybe Movie) (Maybe (PList MovieTrie)) deriving (Show)

-- intToVec :: Int -> (Vector Int)
-- intToVec i = let 
--             remainder = mod i 10
--             quotient = div i 10
--             in if(quotient == 0) then singleton remainder
--                 else append   (intToVec quotient) (singleton remainder)
-- intToChar :: Int -> Char 
-- intToChar i = case i of 
--             0 -> '0'
--             1 -> '1'
--             2 -> '2'
--             3 -> '3'
--             4 -> '4'
--             5 -> '5'
--             6 -> '6'
--             7 -> '7' 
--             8 -> '8'
--             9 -> '9'
-- intToText :: (Vector Int) -> Text 
-- intToText i = if (length i == 1) then 
-- movieToText :: Movie -> Text 
-- movieToText m = case m of 
--                     Empty -> "empty Movie"
--                     Movie c title date director wrriters castinfo movietags rating ->
mkMovieContent :: Text -> Movie
mkMovieContent t = 
    let 
        movietitle = t
        rdate =  (getRandomString 5)
        director = (getRandomString 6)
        writer = Cons  (getRandomString 5) Nil
        cast = Cons  (getRandomString 5) Nil
        movietag =  Cons (getRandomString 5) Nil
        rating = 5
    in Movie movietitle rdate director writer cast movietag rating 

--insert a movie into movieTrie
insertMovie :: Text -> (Maybe Char) -> Movie -> MovieTrie -> MovieTrie 
insertMovie t c m mt = 
    if (length t == 0) 
    then case mt of 
                Root -> MovieTrie c (Just True) (Just m) Nothing
                MovieTrie c ismovie movie cmovieTrie -> MovieTrie c (Just True) (Just m) cmovieTrie
    else
    case mt of 
        Root -> MovieTrie c (Just False) Nothing  (Just (Cons (insertMovie (tail t) (Just (head t)) m Root) Nil))
        MovieTrie c ismovie movie cmovieTrie -> MovieTrie c ismovie movie (Just (insert_Mhelper t m (fromMaybe Nil cmovieTrie)))
                                                    
movieGetChar :: MovieTrie -> Maybe Char
movieGetChar mt = case mt of
    Root -> Nothing
        -- let _ = printsym (quote "nothing")
        -- in Nothing 
    MovieTrie c ismovie movie lmt -> c
    -- let _ = printchar (fromMaybe ' ' c)
    -- in c

insert_Mhelper :: Text -> Movie -> (PList MovieTrie) -> (PList MovieTrie)
insert_Mhelper t m lmt = 
    case lmt of 
        Nil -> Cons (insertMovie (tail t) (Just (head t)) m Root) Nil
        Cons x xs -> if (fromMaybe ' ' (movieGetChar x)) *==* head t then Cons (insertMovie (tail t) (Just (head t)) m x) xs
                    else Cons x (insert_Mhelper t m xs)

deleteMovie :: Text -> MovieTrie -> MovieTrie 
deleteMovie t mt = 
    if (length t == 0)
        then case mt of 
            Root -> mt 
            MovieTrie c ismovie movie cmovieTrie -> if (fromMaybe False ismovie) then MovieTrie c (Just False) (Nothing) cmovieTrie
                                                    else MovieTrie c ismovie movie cmovieTrie
    else 
    case mt of 
        Root -> Root 
        MovieTrie c ismovie movie cmovieTrie -> MovieTrie c ismovie movie (Just (delete_Mhelper t (fromMaybe Nil cmovieTrie)))
    

delete_Mhelper :: Text -> (PList MovieTrie) -> (PList MovieTrie)
delete_Mhelper t lmt = 
    case lmt of 
        Nil -> Nil 
        Cons x xs -> if(fromMaybe ' ' (movieGetChar x)) *==* head t then Cons (deleteMovie (tail t) x) xs
                    else Cons x (delete_Mhelper t xs)
--given movietitle, find movie return empty if not found
searchMovieTitle :: Text  -> MovieTrie -> Movie 
searchMovieTitle t mt = 
    if (length t == 0) then case mt of 
                                Root -> Empty 
                                MovieTrie c ismovie movie cmovieTrie -> if (fromMaybe False ismovie) then (fromMaybe Empty movie) else Empty
    else
    case mt of
        Root -> Empty 
        MovieTrie c ismovie movie cmovieTrie -> if (isNothing cmovieTrie) then Empty
                                                    else 
                                                    let 
                                                    a = fromMaybe Nil cmovieTrie
                                                    in 
                                                    case a of 
                                                        Nil -> Empty 
                                                        Cons x xs -> search_Mhelper t (Cons x xs) 

search_Mhelper :: Text -> (PList MovieTrie) -> Movie 
search_Mhelper t lmt = 
    case lmt of
        Nil -> Empty
        Cons x xs -> if (fromMaybe ' ' (movieGetChar x)) *==* (head t) 
                then searchMovieTitle (tail t) x
                    else search_Mhelper t xs

-- searchMovieRating :: Int -> MovieTrie ->(PList Movie) -> (PList Movie)
-- searchMovieTitle i mt lm = 
--     case mt of 
--         Root -> Nil
--         MovieTrie c ismovie movie cmovieTrie -> 
--             let 
--                 rating = getMovieRating (fromMaybe Empty movie)
--             in if (rating > i) then Cons (fromMaybe Empty movie) (Search_MRhelper i cmovieTrie )
--                 else Search_MRhelper i cmovieTrie

-- search_MRhelper :: Int -> (PList MovieTrie) -> (PList Movie) -> (PList Movie) 

-- getMovieRating :: Movie -> Int
-- getMovieRating m = case m of 
--     Empty -> 0
--     Movie movietitle releasedate director writers casinfo movitags rating -> rating

-- generateNode :: Char -> MovieTrie -> MovieTrie
-- generateNode a mt = 
-- insertMovie :: Text -> MovieTrie -> MovieTrie
-- insertMovie title mt = 
--     if isEmpty title then mt
--     else if mt == End then
--         let 
--             a = head title
--             b = tail title
--             curNode = MovieTrie Nothing (singleton a) insertMovie b End
--         in curNode

isEmptyM :: Movie -> Bool 
isEmptyM m = case m of
    Empty -> True 
    Movie _ _ _ _ _ _ _ ->False

genMovieList :: Int -> (PList Text)
genMovieList i =
    if (i == 0) 
        then Nil 
    else
        let 
            a = mod rand 10
            t = getRandomString a
            nt = genMovieList (i - 1)
        in Cons t nt

consMovieTrie :: (PList Text) -> MovieTrie ->MovieTrie
consMovieTrie lt mt = 
    case lt of 
        Nil -> mt 
        Cons x xs -> 
            let     
                movieContent = mkMovieContent x 
            in consMovieTrie xs (insertMovie x Nothing movieContent mt)