module GenerateLayout3 where
import Basics

type Text = Vector Char

mkBlogs_layout3 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout3 contentfiles tagfiles length =
   if length < 0 then End
   else 
      let select  = (mod length 10)
          def     = "default file"
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft
          rst     = mkBlogs_layout3 contentfiles tagfiles (length - 1)
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc
          header  = Header (getRandomString 5)
          blogID  = ID (10 - (mod length 10))
          author  = Author (getRandomString 5)
          date    = Date (getRandomString 5)           
         in Layout3 tags rst content header blogID author date