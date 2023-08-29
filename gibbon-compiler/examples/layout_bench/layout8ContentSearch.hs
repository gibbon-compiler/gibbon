import Basics
import GenerateLayout8

type Text   = Vector Char

emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End
      Layout8 content rst id author date header tags -> let
                                                            newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                         in Layout8 newContent newRst id author date header tags


-- main function 
gibbon_main = 
   let 
       blogs = mkBlogs_layout8 1000
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInContent keyword blogs
   in (blogLength newblgs) == 1000 
