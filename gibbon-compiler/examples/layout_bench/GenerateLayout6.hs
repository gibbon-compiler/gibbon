module GenerateLayout6 where
import Basics

type Text = Vector Char

mkBlogs_layout6 :: Int -> Blog
mkBlogs_layout6 length =
   if length <= 0 then End
   else 
      let
          header =  (Header (getRandomString 5))
          id = (ID (10 - (mod length 10)))
          author = (Author (getRandomString 5))
          date   = (Date (getRandomString 5))
          content = (Content (Plain (mkRandomInlineList 50)))
          rst     = (mkBlogs_layout6 (length - 1))
          tags    = (TagList (mkSomeTags 10))
         in Layout6 header id author date content rst tags
