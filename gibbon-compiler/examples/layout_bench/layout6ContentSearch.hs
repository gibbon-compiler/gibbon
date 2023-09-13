import Basics
import GenerateLayout6

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout6 header id author date content rst tags -> let 
                                                            newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout6 header id author date newContent newRst tags




-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout6 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in blogLength newblgs == 1000
