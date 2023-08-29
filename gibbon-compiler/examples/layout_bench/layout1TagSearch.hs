import Basics
import GenerateLayout1

type Text = Vector Char


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
   let 
       blogs = mkBlogs_layout1  40
       keyword :: Vector Char  
       keyword = "a"
       newblgs = emphKeywordInTag keyword blogs
   in blogLength newblgs == blogLength blogs
