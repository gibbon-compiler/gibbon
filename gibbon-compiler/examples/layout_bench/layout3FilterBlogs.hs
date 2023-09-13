import Basics
import GenerateLayout3

type Text = Vector Char


filterByKeywordInTagList :: Text -> Blog -> Blog 
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout3 tags rst content header id author date -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                    let newRst  = filterByKeywordInTagList keyword rst
                                                                                                      in Layout3 tags newRst content header id author date
                                                                                                   else filterByKeywordInTagList keyword rst 


checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout3 tags rst content header id author date -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst)                                                                                                   
                                                                                                   
-- main function 
gibbon_main = 
   let
       blogs     = mkBlogs_layout3  100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
