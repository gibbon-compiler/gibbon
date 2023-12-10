import Basics
import GenerateLayout4

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout4 tags content rst header id author date -> let 
                                                            newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout4 tags newContent newRst header id author date 


-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout4  1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in blogLength newblgs == 1000
