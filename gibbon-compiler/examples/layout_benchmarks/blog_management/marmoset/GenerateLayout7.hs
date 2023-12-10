module GenerateLayout7 where
import Basics

type Text = Vector Char

mkBlogs_layout7 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout7 contentfiles tagfiles length =
   if length < 0 then End
   else 
      let select  = (mod length 10)
          def     = "default file" 
          rst     = mkBlogs_layout7 contentfiles tagfiles (length - 1)
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc                                
          header  = Header (getRandomString 5)
          blogID  = ID (10 - (mod length 10))
          author  = Author (getRandomString 5)
          date    = Date (getRandomString 5)
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft           
         in Layout7 rst content header blogID author date tags