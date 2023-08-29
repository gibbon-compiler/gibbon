import Basics
import GenerateLayout7

type Text = Vector Char


filterByKeywordInTagList :: Text -> Blog -> Blog 
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout7 rst content header id author date tags -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                     let newRst  = filterByKeywordInTagList keyword rst
                                                                                                      in Layout7 newRst content header id author date tags
                                                                                                   else filterByKeywordInTagList keyword rst 

                                                                                                   
checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout7 rst content header id author date tags -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst)                                                                                                       
                                                                                                   
                                                                                                   
                                                                                                   
-- main function 
gibbon_main = 
   let 
       blogs     = mkBlogs_layout7 100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
