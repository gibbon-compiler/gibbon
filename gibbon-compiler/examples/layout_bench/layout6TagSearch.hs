import Basics
import GenerateLayout6
type Text   = Vector Char



emphKeywordInTag :: Text -> Blog -> Blog
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout6 header id author date content rst tags -> let present     = searchBlogTags keyword tags
                                                                                        in if present then 
                                                                                                let newContent  = case content of 
                                                                                                                         Content block -> Content (emphasizeKeywordInBlock keyword block) 
                                                                                                    newRst      = emphKeywordInTag keyword rst 
                                                                                                  in Layout6 header id author date newContent newRst tags
                                                                                           else
                                                                                            let newRst = emphKeywordInTag keyword rst 
                                                                                              in Layout6 header id author date content newRst tags
                                                                                         


gibbon_main = 
    let 
        blogs     = mkBlogs_layout6 40
        keyword :: Vector Char  
        keyword = "a"
        newblgs = emphKeywordInTag keyword blogs
    in blogLength newblgs == blogLength blogs
