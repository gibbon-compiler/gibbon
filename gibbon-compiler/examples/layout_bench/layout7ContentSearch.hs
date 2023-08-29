import Basics
import GenerateLayout7

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout7 rst content header id author date tags -> let 
                                                            newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block) 
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout7 newRst newContent header id author date tags 



-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout7 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in blogLength newblgs == 1000
