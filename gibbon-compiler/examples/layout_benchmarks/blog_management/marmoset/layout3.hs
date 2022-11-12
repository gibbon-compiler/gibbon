import Dep

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout3 tags rst content header id author date -> let present = searchBlogContent keyword content 
                                                            newContent = emphasizeBlogContent keyword content present 
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout3 tags newRst (copyPacked newContent) header id author date 


-- main function 
gibbon_main = 
   let --blogs  = mkBlogs_layout3 200000 0 1200                       -- mkBlogs_layout1 length start_id tag_length
       --keyword = (getRandomString 2)                                -- some random keyword
       --new_blogs = iterate (emphKeywordInContent keyword blogs)
       --_          = printsym (quote "NEWLINE")
       --_          = printsym (quote "NEWLINE") 
       --_          = printPacked new_blogs1
       --_          = printsym (quote "NEWLINE")
       --_          = printsym (quote "NEWLINE")
       blogs = mkBlogs_layout3 10
       _ = printPacked blogs
       keyword :: Vector Char  
       keyword = "feelings"
       newblgs = iterate (emphKeywordInContent keyword blogs)
       _ = printPacked newblgs
   in ()