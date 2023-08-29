import Basics 
import GenerateLayout1

type Text = Vector Char

filterByKeywordInTagList :: Text -> Blog -> Blog 
filterByKeywordInTagList keyword blogs = case blogs of 
                                            End -> End 
                                            Layout1 header id author date content tags rst -> let present = searchBlogTags keyword tags
                                                                                                in if present then 
                                                                                                     let newRst  = filterByKeywordInTagList keyword rst
                                                                                                      in Layout1 header id author date content tags newRst
                                                                                                   else filterByKeywordInTagList keyword rst 
                                                                                                   
checkBlogs :: Text -> Blog -> Bool 
checkBlogs keyword blogs = case blogs of 
                                            End -> True
                                            Layout1 header id author date content tags rst -> let present = searchBlogTags keyword tags
                                                                                                in present && (checkBlogs keyword rst) 
                                                

-- main function 
gibbon_main = 
   let 
       blogs     = mkBlogs_layout1 100
       keyword :: Vector Char  
       keyword = "a"
       newblgs = filterByKeywordInTagList keyword blogs
   in checkBlogs keyword newblgs
