import Dep

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout5 rst tags content header id author date -> let --present = searchBlogContent keyword content 
                                                            newContent = emphasizeBlogContent' keyword content --present 
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout5 (newRst) (copyPacked tags) (copyPacked newContent) (header) id author date 



-- main function 
gibbon_main = 
   let --blogs  = mkBlogs_layout5 200000 0 1200                       -- mkBlogs_layout1 length start_id tag_length
       --keyword = (getRandomString 2)                                -- some random keyword
       --new_blogs = iterate (emphKeywordInContent keyword blogs)
       --_          = printsym (quote "NEWLINE")
       --_          = printsym (quote "NEWLINE") 
       --_          = printPacked new_blogs1
       --_          = printsym (quote "NEWLINE")
       --_          = printsym (quote "NEWLINE")
       fc1, fc2, fc3, fc4, fc5, fc6, fc7, fc8, fc9, fc10 :: Text
       ft1, ft2, ft3, ft4, ft5, ft6, ft7, ft8, ft9, ft10 :: Text
       fc1       = readArrayFile (Just ("blog1/blog1Out.txt",  5000))
       fc2       = readArrayFile (Just ("blog2/blog2Out.txt",  5000)) 
       fc3       = readArrayFile (Just ("blog3/blog3Out.txt",  5000))
       fc4       = readArrayFile (Just ("blog4/blog4Out.txt",  5000))
       fc5       = readArrayFile (Just ("blog5/blog5Out.txt",  5000)) 
       fc6       = readArrayFile (Just ("blog6/blog6Out.txt",  5000)) 
       fc7       = readArrayFile (Just ("blog7/blog7Out.txt",  5000))
       fc8       = readArrayFile (Just ("blog8/blog8Out.txt",  5000))
       fc9       = readArrayFile (Just ("blog9/blog9Out.txt",  5000))
       --fc10      = readArrayFile (Just ("blog10/blog10Out.txt",  82270))
       ft1       = readArrayFile (Just ("blog1/blog1Tag.txt", 500))
       ft2      = readArrayFile (Just ("blog2/blog2Tag.txt", 500))
       ft3      = readArrayFile (Just ("blog3/blog3Tag.txt", 500))
       ft4      = readArrayFile (Just ("blog4/blog4Tag.txt", 500))
       ft5      = readArrayFile (Just ("blog5/blog5Tag.txt", 500))
       ft6      = readArrayFile (Just ("blog6/blog6Tag.txt", 500))
       ft7      = readArrayFile (Just ("blog7/blog7Tag.txt", 500))
       ft8      = readArrayFile (Just ("blog8/blog8Tag.txt", 500))
       ft9      = readArrayFile (Just ("blog9/blog9Tag.txt", 500))
       --ft10      = readArrayFile (Just ("blog10/blog10Tag.txt", 3204))
       lfc      = mkListFiles fc1 fc2 fc3 fc4 fc5 fc6 fc7 fc8 fc9 9
       ltc      = mkListFiles ft1 ft2 ft3 ft4 ft5 ft6 ft7 ft8 ft9 9
       blogs = mkBlogs_layout5 lfc ltc 10000
       --_ = printPacked blogs
       --_ = printsym (quote "NEWLINE")
       --_ = printsym (quote "NEWLINE")
       keyword :: Vector Char  
       keyword = "feelings"
       newblgs = iterate (emphKeywordInContent keyword blogs)
       --_ = printPacked newblgs
       --_ = printsym (quote "NEWLINE")
       --_ = printsym (quote "NEWLINE")
   in ()
