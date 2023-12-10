module GenerateLayout8 where
import Basics

type Text = Vector Char


mkBlogs_layout8 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout8 contentfiles tagfiles length = 
   if length < 0 then End 
   else 
      let select  = (mod length 10)
          def     = "default file"
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc
          rst     = mkBlogs_layout8 contentfiles tagfiles (length - 1)
          id      = ID (10 - (mod length 10)) 
          author  = Author (getRandomString (mod rand 9))
          date    = Date (getRandomString (mod rand 9))
          header  = Header (getRandomString (mod rand 9))
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft
       in Layout8 content rst id author date header tags