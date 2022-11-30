module GenerateLayout6 where
import Basics

type Text = Vector Char

mkBlogs_layout6 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout6 contentfiles tagfiles length =
   if length < 0 then End
   else 
      let select  = (mod length 10)
          def     = "default file" 
          header  = Header (getRandomString 5)          
          blogID  = ID (10 - (mod length 10))
          author  = Author (getRandomString 5)
          date    = Date (getRandomString 5)
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc              
          rst     = mkBlogs_layout6 contentfiles tagfiles (length - 1)
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft        
         in Layout6 header blogID author date content rst tags