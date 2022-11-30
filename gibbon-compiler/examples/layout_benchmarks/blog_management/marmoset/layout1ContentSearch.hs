import Basics
import GenerateLayout1

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout1 header id author date content tags rst -> let --present = searchBlogContent keyword content
                                                            --_ = printsym (quote "NEWLINE") 
                                                            --_       = printbool present
                                                            --_ = printsym (quote "NEWLINE")
                                                            newContent = emphasizeBlogContent' keyword content
                                                            --_ = printsym (quote "NEWLINE")
                                                            --_          = printPacked newContent
                                                            --_ = printsym (quote "NEWLINE") 
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout1 (header) (id) (author) (copyPacked date) (copyPacked newContent) (copyPacked tags)  (copyPacked newRst)

-- main function 
gibbon_main = 
   let --blogs  = mkBlogs_layout1 200 0 12                       -- mkBlogs_layout1 length start_id tag_length
       --f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 :: Vector Char
       --f1      = readArrayFile (Just ("blog1Out.txt",  502))
       --f2      = readArrayFile (Just ("blog2Out.txt",  400))
       --f3      = readArrayFile (Just ("blog3Out.txt",  340))
       --f4      = readArrayFile (Just ("blog4Out.txt",  347))
       --f5      = readArrayFile (Just ("blog5Out.txt",  452))
       --f6      = readArrayFile (Just ("blog6Out.txt",  260))
       --f7      = readArrayFile (Just ("blog7Out.txt",  395))
       --f8      = readArrayFile (Just ("blog8Out.txt",  404)) 
       --f9      = readArrayFile (Just ("blog9Out.txt",  278))
       --f10     = readArrayFile (Just ("blog10Out.txt", 299))
       --_      = printVec (\i -> printchar i) f1
       --_      = printVec (\i -> printchar i) f2
       --_      = printVec (\i -> printchar i) f3 
       --_      = printVec (\i -> printchar i) f4
       --_      = printVec (\i -> printchar i) f5
       --_      = printVec (\i -> printchar i) f6
       --_      = printVec (\i -> printchar i) f7
       --_      = printVec (\i -> printchar i) f8
       --_      = printVec (\i -> printchar i) f9
       --_      = printVec (\i -> printchar i) f10
       --block1  = fileToContent f1  (singleton (nth f1  0)) Nil 1 (vlength f1 )
       --block2  = fileToContent f2  (singleton (nth f2  0)) Nil 1 (vlength f2 )
       --block3  = fileToContent f3  (singleton (nth f3  0)) Nil 1 (vlength f3 )
       --block4  = fileToContent f4  (singleton (nth f4  0)) Nil 1 (vlength f4 )
       --block5  = fileToContent f5  (singleton (nth f5  0)) Nil 1 (vlength f5 )
       --block6  = fileToContent f6  (singleton (nth f6  0)) Nil 1 (vlength f6 )
       --block7  = fileToContent f7  (singleton (nth f7  0)) Nil 1 (vlength f7 )
       --block8  = fileToContent f8  (singleton (nth f8  0)) Nil 1 (vlength f8 )
       --block9  = fileToContent f9  (singleton (nth f9  0)) Nil 1 (vlength f9 )
       --block10 = fileToContent f10 (singleton (nth f10 0)) Nil 1 (vlength f10)
       --_     = printPacked block1
       --_     = printPacked block2
       --_     = printPacked block3
       --_     = printPacked block4
       --_     = printPacked block5
       --_     = printPacked block6
       --_     = printPacked block7
       --_     = printPacked block8
       --_     = printPacked block9
       --_     = printPacked block10 
      -- keyword = (getRandomString 2)                                -- some random keyword
      -- new_blogs = iterate (emphKeywordInContent keyword blogs)
       --_          = printsym (quote "NEWLINE")
       --_          = printsym (quote "NEWLINE") 
       --_          = printPacked new_blogs1
       --_          = printsym (quote "NEWLINE")
       --_          = printsym (quote "NEWLINE")
       --content :: BlogContent
       --tags :: BlogTags
       --(content, tags) = mkContentFromText (mod rand 10)
       --_       = printPacked content
       --_       = printPacked tags
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
       blogs = mkBlogs_layout1 lfc ltc 10000
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
