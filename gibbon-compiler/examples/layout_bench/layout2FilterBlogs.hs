import Basics
import GenerateLayout2

type Text = Vector Char


filterByKeywordInTagList :: Text -> Blog -> Blog
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout2 content tags rst header id author date -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                    let newRst  = filterByKeywordInTagList keyword rst
                                                                                                     in Layout2 content tags newRst header id author date
                                                                                                   else filterByKeywordInTagList keyword rst
                                                                                                   
                                                                                                   
checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout2 content tags rst header id author date -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst)                                                                                                   
                                                                                                        
gibbon_main = 
   let 
       blogs     = mkBlogs_layout2  100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
