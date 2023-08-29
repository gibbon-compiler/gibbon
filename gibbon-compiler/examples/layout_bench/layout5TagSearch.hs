import Basics
import GenerateLayout5

type Text   = Vector Char



emphKeywordInTag :: Text -> Blog -> Blog 
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout5 rst tags content header id author date -> let present     = searchBlogTags keyword tags
                                                                                       in if present then 
                                                                                              let newContent  = case content of 
                                                                                                                         Content block -> Content (emphasizeKeywordInBlock keyword block) 
                                                                                                  newRst      = emphKeywordInTag keyword rst 
                                                                                                in Layout5 newRst tags newContent header id author date
                                                                                          else 
                                                                                            let newRst = emphKeywordInTag keyword rst 
                                                                                              in Layout5 newRst tags content header id author date


gibbon_main = 
    let 
        blogs     = mkBlogs_layout5 40
        keyword :: Vector Char  
        keyword = "a"
        newblgs = emphKeywordInTag keyword blogs
    in blogLength newblgs == blogLength blogs
