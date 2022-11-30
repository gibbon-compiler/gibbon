module GenerateLayout1 where
import Basics

type Text = Vector Char




mkBlogs_layout1 :: PList Text -> PList Text -> Int -> Blog
mkBlogs_layout1 contentfiles tagfiles length =
   if length < 0 then End
   else 
      let header  = Header (getRandomString 5)
          blogID  = ID (10 - (mod length 10))
          author  = Author (getRandomString 5)
          date    = Date (getRandomString 5)
          select  = (mod length 10)
          def     = "default file"  -- this is un-necessary and just used for a default value
          fc      = fromMaybe def (nth_plist contentfiles Nothing select)
          content = mkContentFromText fc
          ft      = fromMaybe def (nth_plist tagfiles Nothing select)
          tags    = mkTagsFromText ft
          rst     = mkBlogs_layout1 contentfiles tagfiles (length - 1)
         in Layout1 header blogID author date content tags rst