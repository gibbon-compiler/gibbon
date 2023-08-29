import Basics
import GenerateLayout2

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout2 content tags rst header id author date -> let newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                          in Layout2 newContent tags newRst header id author date
                                                          

-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout2 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in blogLength newblgs == 1000
