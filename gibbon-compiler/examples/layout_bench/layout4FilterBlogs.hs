import Basics
import GenerateLayout4 

type Text = Vector Char


filterByKeywordInTagList :: Text -> Blog -> Blog
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout4 tags content rst header id author date -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                    let newRst  = filterByKeywordInTagList keyword rst
                                                                                                      in Layout4 tags content newRst header id author date
                                                                                                   else filterByKeywordInTagList keyword rst 
                                                


checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout4 tags content rst header id author date -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst)                                                 
                                                
-- main function 
gibbon_main = 
   let 
       blogs     = mkBlogs_layout4  100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
