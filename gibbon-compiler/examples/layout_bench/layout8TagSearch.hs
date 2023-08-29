import Basics
import GenerateLayout8 

type Text = Vector Char 



emphKeywordInTag :: Text -> Blog -> Blog
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout8 content rst id author date header tags -> let present     = searchBlogTags keyword tags 
                                                                                       in if present then 
                                                                                                let newContent  = case content of 
                                                                                                                        Content block -> Content (emphasizeKeywordInBlock keyword block)
                                                                                                    newRst      = emphKeywordInTag keyword rst 
                                                                                                  in Layout8 newContent newRst id author date header tags
                                                                                          else
                                                                                            let newRst = emphKeywordInTag keyword rst 
                                                                                             in Layout8 content newRst id author date header tags
                                                                                        

gibbon_main = 
    let 
        blogs     = mkBlogs_layout8 40
        keyword :: Vector Char  
        keyword = "a"
        newblgs = emphKeywordInTag keyword blogs
    in blogLength newblgs == blogLength blogs
