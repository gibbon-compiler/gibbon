import Basics
import GenerateLayout4

type Text = Vector Char 


emphKeywordInTag :: Text -> Blog -> Blog 
emphKeywordInTag keyword blogs = case blogs of 
                                    End -> End
                                    Layout4 tags content rst header id author date -> let present     = searchBlogTags keyword tags
                                                                                          newContent  = emphasizeBlogContent keyword content
                                                                                          newRst = emphKeywordInTag keyword rst   
                                                                                        in Layout4 tags newContent newRst header id author date


gibbon_main = 
    let 
        blogs     = mkBlogs_layout4  40
        keyword :: Vector Char  
        keyword = "a"
        newblgs = emphKeywordInTag keyword blogs
    in blogLength newblgs == blogLength blogs
