module GenerateLayout8 where
import Basics

type Text = Vector Char


mkBlogs_layout8 :: Int -> Blog
mkBlogs_layout8 length = 
   if length <= 0 then End 
   else 
      let
          content = (Content (Plain (mkRandomInlineList 50)))
          rst     = (mkBlogs_layout8 (length - 1))
          id      = (ID (10 - (mod length 10)))
          author  = (Author (getRandomString 5))
          date    = (Date (getRandomString 5))
          header  = (Header (getRandomString 5))
          tags    = (TagList (mkSomeTags 10))       
         in Layout8 content rst id author date header tags    
