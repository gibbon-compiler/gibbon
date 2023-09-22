import Basics
import GenerateLayout1 

type Text = Vector Char 


emphKeywordInContent :: Text -> Blog -> Blog
emphKeywordInContent keyword blogs = 
   case blogs of 
      End -> End 
      Layout1 header id author date content tags rst -> let newContent = case content of 
                                                                               Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                            newRst     = emphKeywordInContent keyword rst 
                                                        in Layout1 header id author date newContent tags newRst
                                                        
                                                        

filterByKeywordInTagList :: Text -> Blog -> Blog 
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout1 header id author date content tags rst -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                     let newRst  = filterByKeywordInTagList keyword rst
                                                                                                      in Layout4 tags content newRst header id author date
                                                                                                   else filterByKeywordInTagList keyword rst 
                                                                                                   

emphKeywordInTag :: Text -> Blog -> Blog
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout1 header id author date content tags rst -> let present = searchBlogTags keyword tags
                                                                                          in if (present) 
                                                                                             then let newContent  = case content of 
                                                                                                                         Content block -> Content (emphasizeKeywordInBlock keyword block) 
                                                                                                      newRst      = emphKeywordInTag keyword rst
                                                                                                    in Layout1 header id author date newContent tags newRst
                                                                                             else
                                                                                               let newRst = emphKeywordInTag keyword rst
                                                                                                 in Layout1 header id author date content tags newRst
                                                                                                 
                                                                                                 
-- main function 
gibbon_main = 
   let blogs = mkBlogs_layout1 2
       keyword :: Vector Char  
       keyword = "a"
       newblgs   = emphKeywordInContent keyword blogs
       newblgs'  = emphKeywordInTag keyword newblgs 
       newblgs'' = filterByKeywordInTagList keyword newblgs'
   in printPacked newblgs''
