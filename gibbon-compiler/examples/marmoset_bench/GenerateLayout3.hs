module GenerateLayout3 where
import Basics

type Text = Vector Char

mkBlogs_layout3 :: Int -> Blog
mkBlogs_layout3 length =
   if length <= 0 then End
   else 
      let      
          tags =   (TagList (mkSomeTags 10))
          rst  = (mkBlogs_layout3 (length - 1))
          content = (Content (Plain (mkRandomInlineList 50)))
          header  = (Header (getRandomString 5))
          id      = (ID (10 - (mod length 10)))
          author = (Author (getRandomString 5))
          date   = (Date (getRandomString 5))
         in Layout3 tags rst content header id author date
