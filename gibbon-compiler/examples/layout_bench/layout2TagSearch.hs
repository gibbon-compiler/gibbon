import Basics
import GenerateLayout2

type Text = Vector Char 


emphKeywordInTag :: Text -> Blog -> Blog 
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout2 content tags rst header id author date -> let present = searchBlogTags keyword tags
                                                                                          in if (present) 
                                                                                             then let newContent  = case content of 
                                                                                                                         Content block -> Content (emphasizeKeywordInBlock keyword block) 
                                                                                                      newRst      = emphKeywordInTag keyword rst
                                                                                                    in Layout2 newContent tags newRst header id author date
                                                                                             else
                                                                                               let newRst = emphKeywordInTag keyword rst
                                                                                                in Layout2 content tags newRst header id author date


gibbon_main = 
    let 
        blogs     = mkBlogs_layout2  40
        keyword :: Vector Char  
        keyword = "a"
        newblgs = emphKeywordInTag keyword blogs
    in blogLength newblgs == blogLength blogs
