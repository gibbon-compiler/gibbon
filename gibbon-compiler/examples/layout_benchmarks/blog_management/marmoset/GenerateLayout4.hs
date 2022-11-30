module GenerateLayout4 where
import Basics

type Text = Vector Char

mkBlogs_layout4 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout4 contentfiles tagfiles length =
   if length < 0 then End
   else 
      let select  = (mod length 10)
          def     = "default file"
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc
          rst     = mkBlogs_layout4 contentfiles tagfiles (length - 1)        
          header  = Header (getRandomString 5)        
          blogID  = ID (10 - (mod length 10))
          author  = Author (getRandomString 5)
          date    = Date (getRandomString 5)           
         in Layout4 tags content rst header blogID author date