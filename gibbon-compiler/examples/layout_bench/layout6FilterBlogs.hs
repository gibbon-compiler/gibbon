import Basics
import GenerateLayout6

type Text = Vector Char


filterByKeywordInTagList :: Text -> Blog -> Blog 
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout6 header id author date content rst tags -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                    let newRst  = filterByKeywordInTagList keyword rst
                                                                                                      in Layout6 header id author date content newRst tags
                                                                                                   else filterByKeywordInTagList keyword rst 

                                                                                                   
checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout6 header id author date content rst tags -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst)                                                                                                    
                                                                                                   
-- main function 
gibbon_main = 
   let 
       blogs     = mkBlogs_layout6 100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
