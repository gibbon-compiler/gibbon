import Basics
import GenerateLayout7

type Text   = Vector Char


emphKeywordInTag :: Text -> Blog -> Blog  
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout7 rst content header id author date tags -> let present     = searchBlogTags keyword tags
                                                                                        in if present then 
                                                                                            let newContent  = case content of 
                                                                                                                         Content block -> Content (emphasizeKeywordInBlock keyword block) 
                                                                                                newRst      = emphKeywordInTag keyword rst 
                                                                                              in Layout7 newRst newContent header id author date tags
                                                                                           else 
                                                                                            let newRst = emphKeywordInTag keyword rst 
                                                                                             in Layout7 newRst content header id author date tags
                                                                                            

gibbon_main = 
    let 
        blogs     = mkBlogs_layout7 40
        keyword :: Vector Char  
        keyword = "a"
        newblgs = emphKeywordInTag keyword blogs
    in blogLength newblgs == blogLength blogs
