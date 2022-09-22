module Main where

import Gibbon.Prelude
import Gibbon.PList
import Gibbon.Vector 

type Text   = Vector Int

type Target = (Text, Text)

type Attr   = (Text, (PList Text), (PList (Text, Text)))

--type Format = Format Text

data Inline =     Str Text
                | Emph (PList Inline)
                | Underline (PList Inline)
                | Strong (PList Inline)
                | Strikeout (PList Inline)
                | Superscript (PList Inline)
                | Subscript (PList Inline)
                | SmallCaps (PList Inline)
             -- | Quoted QuoteType (Vector Inline)
             -- | Cite [Citation] (Vector Inline)
             -- | Code Attr Text
                | Space
                | SoftBreak
                | LineBreak
             -- | Math MathType Text
             -- | RawInline Format Text
             -- | Link Attr (Vector Inline) Target
             -- | Image Attr (Vector Inline) Target
                | Note (PList Block)
             -- | Span Attr (Vector Inline)

data Block =      Plain (PList Inline)
                | Para  (PList Inline)
             -- | LineBlock (PList (PList Inline))
             -- | CodeBlock Attr Text
             -- | RawBlock Format Text
                | BlockQuote (PList Block)
             -- | OrderedList ListAttributes [[Block]]
             -- | BulletList (PList (PList Block))
             -- | DefinitionList PList ( PList Inline , PList (PList Block) ) ---> This is resulting in a compile time error (TODO: Will DEBUG this)
             -- | Header Int Attr (Vector Inline)
                | HorizontalRule
             -- | Table Attr Caption [ColSpec] TableHead [TableBody] TableFoot
             -- | Div Attr (Vector Block)
                | Null

-- A data type for the elements with-in a Blog. 
data BlogElements =   Header Text
                    | ID Int
                    | Author Text
                    | Date   Text
                    | Content Block
                    | TagList (PList Text) 

-- A data type for a Blog Post
-- This is a Recursive field, with Next Blog contaning the rest of the elements of the blog.
-- This recursive blog just represents a composed Blog.
data Blog = End | Next BlogElements (Blog)

{-

CK: shouldn't this be:

data Blog = (ID Int) (TagList (PList Text)) (Author Text) (Content Block) ...

-}

-- data type for a list of Blogs, (Maybe we can just use a Packed PList here instead?)
data BlogList = None | Nxt Blog (BlogList)

-- Begin functions that will be used to create data structures with random data in it.

-- make an Inline type, option chooses what kind of Inline data type we are creating
mkInline :: Int -> Inline
mkInline option = 
   if option == 0 then (Str (mkText 100))
   else if option == 1 then (Emph (mkInlineList 100))
   else if option == 2 then (Underline (mkInlineList 100))
   else if option == 3 then (Strong (mkInlineList 100))
   else if option == 4 then (Strikeout (mkInlineList 100))
   else if option == 5 then (Superscript (mkInlineList 100))
   else if option == 6 then (Subscript (mkInlineList 100))
   else if option == 7 then (SmallCaps (mkInlineList 100))
   else if option == 8 then Space
   else if option == 9 then SoftBreak
   else if option == 10 then LineBreak 
   else (Note (mkBlockList 100)) 

-- make a list of Inlines
mkInlineList :: Int -> (PList Inline)
mkInlineList length = 
   if length <= 0 then Nil 
   else let item = (mkInline (mod rand 11))
            rst  = mkInlineList (length - 1)
         in Cons item rst

-- make a list of blocks
mkBlockList :: Int -> (PList Block)
mkBlockList length = 
   if length <= 0 then Nil
   else let item = (mkBlock (mod rand 4))
            rst  = mkBlockList (length - 1)
         in Cons item rst

-- make a Block data type with random data
mkBlock :: Int -> Block
mkBlock option = 
   if option == 0 then (Plain (mkInlineList 100))
   else if option == 1 then (Para (mkInlineList 100))
   else if option == 2 then (BlockQuote (mkBlockList 100))
   else if option == 3 then HorizontalRule
   else Null

-- A function to make a list of tags each filled with some random tags
mkTagList :: Int -> (PList Text)
mkTagList length = 
   if length <= 0 then Nil
   else let elem = (mkText 5)
            rst  = mkTagList (length - 1)
          in Cons elem rst

-- A function to make a Blog with some elements with random data. 
mkBlog :: Int -> Int -> Int -> Blog
mkBlog option id tag_length = 
   if option == 0 
      then let header = (Header (mkText 100)) 
               rst    = (mkBlog 1 id tag_length)
            in (Next header (rst))
   else if option == 1 
      then let blog_id = (ID id)
               rst     = (mkBlog 2 id tag_length) 
         in (Next blog_id (rst))
   else if option == 2 
      then let author = (Author (mkText 5))
               rst    = (mkBlog 3 id tag_length)
         in (Next author (rst))  
   else if option == 3 
      then let date = (Date (mkText 5))
               rst  = (mkBlog 4 id tag_length)
         in (Next date (rst))
   else if option == 4 
      then let content = (Content (mkBlock (mod rand 5)))
               rst     = (mkBlog 5 id tag_length)
         in (Next content (rst)) 
   else if option == 5 
      then let taglist = TagList (mkTagList 100)
               rst     = (mkBlog 6 id tag_length)
         in (Next taglist (rst)) 
   else End
          
-- Recursive function to make a list of blogs
mkBlogList :: Int -> BlogList
mkBlogList length = 
   if length <= 0 then None 
   else let blog = (mkBlog 0 length 100)
            rst  = mkBlogList (length - 1)
         in Nxt blog (rst)     

-- Function to make a text string of some length. 
-- First argument takes Length, returns a text string.
mkText :: Int -> Text
mkText length = 
    let string :: Text 
        --string = generate length (\i -> mod rand length)
        string = generate length (\i -> i)
    in string

-- End functions that will be used to create data structures with random data in it.

-- Begin functions to search the content for a particular keyword.
-- If keyword is present highlight that keyword (Emph) in the content 
-- For now to make things simple, consider a keyword in represented via an Int.

-- search for a particular keyword (Int) in a Text blob (Vector Int) 
-- TODO: Replace Text = Vector Int to Vector Char
searchKeywordText :: Int -> Text -> Bool
searchKeywordText keyword text = 
   let len = length text in 
   if len <= 0 then False
   else let front  = head text
            sliced = slice 1 (len - 1) text
         in 
         if front == keyword then (True || searchKeywordText keyword sliced)
         else (False || searchKeywordText keyword sliced)  

-- Tell if a particular keyword exists in the Content field of the blog or not. (search a Block)
-- Question are there characters for Horizontal rule or Null, if so can't just return false for those.
-- Instead will need to have a comparsion of character to those specifically and then return the result. 
isKeywordPresentBlock :: Int -> Block -> Bool
isKeywordPresentBlock keyword contentBlock = 
   case contentBlock of
      Plain list_inline      -> (searchInlineListForKeyword keyword list_inline)
      Para  list_inline      -> (searchInlineListForKeyword keyword list_inline)
      BlockQuote list_block  -> (searchBlockListForKeyword keyword list_block)
      HorizontalRule         -> False
      Null                   -> False

-- Tell if a particular keyword exists in the inline or not. (search a Inline)
isKeywordPresentInline :: Int -> Inline -> Bool
isKeywordPresentInline keyword inline = 
   case inline of 
      Str text                -> (searchKeywordText keyword text)
      Emph list_inline        -> (searchInlineListForKeyword keyword list_inline)
      Underline list_inline   -> (searchInlineListForKeyword keyword list_inline)
      Strong list_inline      -> (searchInlineListForKeyword keyword list_inline)
      Strikeout list_inline   -> (searchInlineListForKeyword keyword list_inline)
      Superscript list_inline -> (searchInlineListForKeyword keyword list_inline)
      Subscript list_inline   -> (searchInlineListForKeyword keyword list_inline) 
      SmallCaps list_inline   -> (searchInlineListForKeyword keyword list_inline) 
      Space                   -> False
      SoftBreak               -> False 
      LineBreak               -> False 
      Note list_block         -> (searchBlockListForKeyword keyword list_block)

-- Search a block list for a particular keyword
searchBlockListForKeyword :: Int -> PList Block -> Bool 
searchBlockListForKeyword keyword block_list = 
   case block_list of 
      Nil             -> False
      Cons block rst  -> (isKeywordPresentBlock keyword block) || (searchBlockListForKeyword keyword rst) 

-- Seach an Inline list for a particular keyword
searchInlineListForKeyword :: Int -> PList Inline -> Bool
searchInlineListForKeyword keyword inline_list = 
   case inline_list of 
      Nil                -> False 
      Cons inline rst    -> (isKeywordPresentInline keyword inline) || (searchInlineListForKeyword keyword rst)

-- search a blog element for a keyword
searchBlogElementForKeyword :: Int -> BlogElements -> Bool 
searchBlogElementForKeyword keyword element = 
   case element of 
      Header text   -> (searchKeywordText keyword text)
      ID val        -> False 
      Author text   -> False 
      Date   text   -> False
      Content block -> (isKeywordPresentBlock keyword block)
      TagList list  -> False

-- search for a keyword in a blog. 
searchBlogForKeyword :: Int -> Blog -> Bool
searchBlogForKeyword keyword blog = 
   case blog of
      End -> False 
      Next element rst -> (searchBlogElementForKeyword keyword element) || (searchBlogForKeyword keyword rst)

-- search for a keyword in a list of blogs
searchBlogsForKeyword :: Int -> BlogList -> Bool
searchBlogsForKeyword keyword blog_list = 
   case blog_list of 
      None          -> False
      Nxt blog rst  -> (searchBlogForKeyword keyword blog) || (searchBlogsForKeyword keyword rst)


-- main function 
gibbon_main = 
   let blog_list = mkBlogList 1
       keyword :: Int 
       keyword = 1
       exists :: Bool 
       exists = searchBlogsForKeyword keyword blog_list
       _      = printsym (quote "Does keyword exist in blogs: ")
       _      = printbool exists 
       _      = printsym (quote "NEWLINE")
   in ()
       

