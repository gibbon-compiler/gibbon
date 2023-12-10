import Basics
import GenerateLayout5

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout5 rst tags content header id author date -> let 
                                                            newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout5 newRst tags newContent header id author date 



-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout5 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in blogLength newblgs == 1000
