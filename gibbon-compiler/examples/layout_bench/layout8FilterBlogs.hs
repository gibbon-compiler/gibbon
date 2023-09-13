import Basics
import GenerateLayout8

type Text = Vector Char


filterByKeywordInTagList :: Text -> Blog -> Blog 
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout8 content rst id author date header tags -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                    let newRst  = filterByKeywordInTagList keyword rst
                                                                                                     in Layout8 content newRst id author date header tags
                                                                                                   else filterByKeywordInTagList keyword rst 


checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout8 content rst id author date header tags -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst)                                                                                                                 
                                                                                                   
                                                                                                   
                                                                                                   
-- main function 
gibbon_main = 
   let 
       blogs     = mkBlogs_layout8 100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
