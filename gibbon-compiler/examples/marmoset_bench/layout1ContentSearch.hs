import Basics
import GenerateLayout1

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout1 header id author date content tags rst -> let newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                        in Layout1 header id author date newContent tags newRst

-- main function 
gibbon_main = 
   let blogs = mkBlogs_layout1 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in (blogLength newblgs) == 1000
