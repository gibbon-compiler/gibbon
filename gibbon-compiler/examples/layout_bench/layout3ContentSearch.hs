import Basics
import GenerateLayout3

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout3 tags rst content header id author date -> let newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout3 tags newRst newContent header id author date 


-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout3 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in blogLength newblgs == 1000
