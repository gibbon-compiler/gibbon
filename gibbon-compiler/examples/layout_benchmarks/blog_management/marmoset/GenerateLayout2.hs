module GenerateLayout2 where
import Basics

type Text = Vector Char

mkBlogs_layout2 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout2 contentfiles tagfiles length =
   if length < 0 then End
   else 
      let select  = (mod length 10)
          def     = "default file"
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft
          rst     = mkBlogs_layout2 contentfiles tagfiles (length - 1)
          header  = Header (getRandomString 5)
          blogID  = ID (10 - (mod length 10))
          author  = Author (getRandomString 5)
          date    = Date (getRandomString 5)                 
         in Layout2 content tags rst header blogID author date 