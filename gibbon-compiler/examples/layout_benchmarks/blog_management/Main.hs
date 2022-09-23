module Main where

import Gibbon.Prelude
import Gibbon.PList
import Gibbon.Vector

type Text   = Vector Char

type Target = (Text, Text)

type Attr   = (Text, (PList Text), (PList (Text, Text)))

--type Format = Format Text

-- For simplicity, we are assuming for this benchmark that data Inline is tokenized at the "word" level.
-- Therefore, The Base case where "Text" is used is going to be a single word, i.e, "Str Text".
data Inline =     Str Text
                | Emph (PList Inline)
                | Underline (PList Inline)
                | Strong (PList Inline)
                | Strikeout (PList Inline)
                | Superscript (PList Inline)
                | Subscript (PList Inline)
                | SmallCaps (PList Inline)
             -- | Quoted QuoteType (PList Inline)
             -- | Cite [Citation] (PList Inline)
             -- | Code Attr Text
                | Space
                | SoftBreak
                | LineBreak
             -- | Math MathType Text
             -- | RawInline Format Text
             -- | Link Attr (PList Inline) Target
             -- | Image Attr (PList Inline) Target
                | Note (PList Block)
             -- | Span Attr (PList Inline)
                deriving (Show)  

data Block =      Plain (PList Inline)
                | Para  (PList Inline)
             -- | LineBlock (PList (PList Inline))
             -- | CodeBlock Attr Text
             -- | RawBlock Format Text
                | BlockQuote (PList Block)
             -- | OrderedList ListAttributes [[Block]]
             -- | BulletList (PList (PList Block))
             -- | DefinitionList PList ( PList Inline , PList (PList Block) ) ---> This is resulting in a compile time error (TODO: Will DEBUG this)
             -- | Header Int Attr (PList Inline)
                | HorizontalRule
             -- | Table Attr Caption [ColSpec] TableHead [TableBody] TableFoot
             -- | Div Attr (PList Block)
                | Null
                deriving (Show)

-- A data type for the elements with-in a Blog Structure. 
data BlogElements =   Header Text
                    | ID Int
                    | Author Text
                    | Date   Text
                    | Content Block
                    | TagList (PList Text) 
                    deriving (Show)

-- A data type for a Blog Post
-- This is a Recursive field, with Next Blog containing the rest of the elements of the blog.
-- This recursive blog just represents a composed Blog (i.e, a Blog composed of its elements).
data Blog =   End 
            | Next BlogElements (Blog) 
            deriving (Show)

-- A data type for a list of Blogs.
data BlogList =   None 
                | Nxt Blog (BlogList)
                deriving (Show)

-- Data structures for a Full Inverted 
-- LocationInfo = (Doc id or address, location/address in document)
-- Mapping      = (keyword as text, List of Docs as LocationInfo tuples)
-- But maybe, Mapping and Location Info should be packed data as well ? If we are to run multiple passes on them?

type LocationInfo  = (Int, Int) 
type Mapping       = (Text, PList Info)
type InvertedTable = PList Mapping

-- Get a random word, based on an Int option
getRandomString :: Int -> Text
getRandomString option = 
    if option == 0 then 
        let str :: Text
            str = "hello"
            in str
    else if option == 1 then
        let str :: Text 
            str = "blah"
            in str
    else if option == 2 then
        let str :: Text 
            str = "nope"
            in str
    else if option == 3 then
        let str :: Text 
            str = "hurray!"
            in str
    else if option == 4 then
        let str :: Text 
            str = "voila!"
            in str
    else if option == 5 then
        let str :: Text 
            str = "cool!"
            in str
    else if option == 6 then
        let str :: Text 
            str = "Hey!"
            in str
    else if option == 7 then
        let str :: Text
            str = "ola"
            in str
    else let str :: Text 
             str = "bye"
             in str

-- Make an Inline type, option chooses what kind of Inline data type we are creating
-- This will Purposefully make Inline lists at a depth of recursion 1, this can be modified to increase the depth of recursion.
-- This function crates the recursive fields. 
mkInline :: Int -> Inline
mkInline option = 
   if option == 0 then (Emph (mkInlineList 100 1))
   else if option == 1 then (Underline (mkInlineList 100 1))
   else if option == 2 then (Strong (mkInlineList 100 1))
   else if option == 3 then (Strikeout (mkInlineList 100 1))
   else if option == 4 then (Superscript (mkInlineList 100 1))
   else if option == 5 then (Subscript (mkInlineList 100 1))
   else if option == 6 then (SmallCaps (mkInlineList 100 1))
   else (Note (mkBlockList 100 1)) 


-- Make an Inline type, option chooses what kind of Inline data type we are creating
-- This creates all the base cases for the inline type 
mkInlineBaseCase :: Int -> Inline
mkInlineBaseCase option = 
   if option == 0 then (Str (getRandomString (mod rand 9)))   -- get a random word
   else if option == 1 then Space
   else if option == 2 then SoftBreak
   else LineBreak 

-- Make a list of Inline data Type.
mkInlineList :: Int -> Int -> (PList Inline)
mkInlineList length base = 
   if length <= 0 then Nil 
   -- If its not base case, then don't stop recursion. 
   else if (base == 0) then 
      let item = (mkInline (mod rand 8))
          rst  = (mkInlineList (length - 1) base)
          in Cons item rst
   -- If its  base case, then stop recursion in Inline data type and only add base cases. 
   else let item = (mkInlineBaseCase (mod rand 4))
            rst  = mkInlineList (length - 1) base 
         in Cons item rst

-- Make a list of blocks
mkBlockList :: Int -> Int -> (PList Block)
mkBlockList length base = 
   if length <= 0 then Nil
   else if (base == 0) then
      let item = (mkBlock (mod rand 3))
          rst  = (mkBlockList (length - 1) base)
      in Cons item rst
   else let item = (mkBlockBaseCase (mod rand 2))
            rst  = (mkBlockList (length - 1) base) 
      in Cons item rst

-- Make a Block data type with random data, make depth of recursion to 1 for now
mkBlock :: Int -> Block
mkBlock option = 
   if option == 0 then (Plain (mkInlineList 100 1))
   else if option == 1 then (Para (mkInlineList 100 1))
   else (BlockQuote (mkBlockList 100 1))

-- Base case for make Block
mkBlockBaseCase :: Int -> Block 
mkBlockBaseCase option = 
   if option == 0 then HorizontalRule
   else Null


-- A function to make a list of tags each filled with some random tags
mkTagList :: Int -> (PList Text)
mkTagList length = 
   if length <= 0 then Nil
   else let elem = (getRandomString (mod rand 9))
            rst  = mkTagList (length - 1)
          in Cons elem rst

-- A function to make a Blog with some elements with random data. 
mkBlog :: Int -> Int -> Int -> Blog
mkBlog option id tag_length = 
   if option == 0 
      then let header = (Header (getRandomString (mod rand 9))) 
               rst    = (mkBlog 1 id tag_length)
            in (Next header (rst))
   else if option == 1 
      then let blog_id = (ID id)
               rst     = (mkBlog 2 id tag_length) 
         in (Next blog_id (rst))
   else if option == 2 
      then let author = (Author (getRandomString (mod rand 9)))
               rst    = (mkBlog 3 id tag_length)
         in (Next author (rst))  
   else if option == 3 
      then let date = (Date (getRandomString (mod rand 9)))
               rst  = (mkBlog 4 id tag_length)
         in (Next date (rst))
   else if option == 4 
      then let content = (Content (mkBlock (mod rand 2)))
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
-- mkText :: Int -> Text
-- mkText length = 
--     let string :: Text
--         string = generate length (\i -> i)
--     in string

-- End functions that will be used to create data structures with random data in it.

-- Begin functions to search the content for a particular keyword.
-- If keyword is present highlight that keyword (Emph) in the content 
-- For now to make things simple, consider a keyword in represented via an Int.

-- search for a particular keyword (Int) in a Text blob (Vector Int) 
-- TODO: Replace Text = Vector Int to Vector Char
-- searchKeywordText :: Int -> Text -> Bool
-- searchKeywordText keyword text = 
--    let len = length text in 
--    if len <= 0 then False
--    else let front  = head text
--             sliced = slice 1 (len - 1) text
--          in 
--          if front == keyword then (True || searchKeywordText keyword sliced)
--          else (False || searchKeywordText keyword sliced)  

-- Maybe use this function to implement such that you can search a keyword in a string of words ? 
-- searchKeywordText :: Text -> Text -> Bool
-- searchKeywordText keyword text = False

-- Function to compare two words, each represented by a Vector Char. 
compareWord :: Text -> Text -> Bool
compareWord vec1 vec2 = 
   let len1        = length vec1 
       len2        = length vec2
       compare_len = if (len1 == len2) then True else False     
   in if (compare_len) then (cmp 0 len1 vec1 vec2) else False

-- Compare for 2 Vector Char (Text) if their length is same. 
cmp :: Int -> Int -> Vector Char -> Vector Char -> Bool
cmp start end vec1 vec2 =
   if (start < end) then 
      let a       = nth vec1 start
          b       = nth vec2 start
          eq      = True -- if (a == b) then True else False -- For now this is not complemented, TODO: Implement Character comparison. 
          recurse = cmp (start+1) end vec1 vec2
         in (eq && recurse) 
      else True

-- search a taglist for some keyword
searchTagList :: Text -> PList Text -> Bool 
searchTagList keyword taglist = case taglist of 
   Nil -> False 
   Cons word rst -> (compareWord keyword word) || (searchTagList keyword rst)

-- Search if a particular Tag exists in the Tag list of the blog
searchBlogElementForTagKeyword :: Text -> BlogElements -> Bool 
searchBlogElementForTagKeyword keyword element = 
   case element of 
      Header text   -> False
      ID val        -> False 
      Author text   -> False 
      Date   text   -> False
      Content block -> False
      TagList list  -> (searchTagList keyword list)

-- Search for a keyword in a blog. 
searchBlogForTagKeyword :: Text -> Blog -> Bool
searchBlogForTagKeyword keyword blog = 
   case blog of
      End -> False 
      Next element rst -> (searchBlogElementForTagKeyword keyword element) || (searchBlogForTagKeyword keyword rst)

-- Filter Blogs with a particular keyword
filterBlogsBasedOnTagKeyword :: Text -> BlogList -> BlogList
filterBlogsBasedOnTagKeyword keyword blog_list = 
   case blog_list of 
      None          -> None
      Nxt blog rst  -> let exists = searchBlogForTagKeyword keyword blog 
                           rst'   = filterBlogsBasedOnTagKeyword keyword rst
                           in if (exists) then (Nxt blog rst')
                              else rst'

-- Tell if a particular keyword exists in the Content field of the blog or not. (search a Block)
isKeywordPresentBlock :: Text -> Block -> Bool
isKeywordPresentBlock keyword contentBlock = 
   case contentBlock of
      Plain list_inline      -> (searchInlineListForKeyword keyword list_inline)
      Para  list_inline      -> (searchInlineListForKeyword keyword list_inline)
      BlockQuote list_block  -> (searchBlockListForKeyword keyword list_block)
      HorizontalRule         -> False
      Null                   -> False

-- Tell if a particular keyword exists in the inline or not. (search a Inline)
isKeywordPresentInline :: Text -> Inline -> Bool
isKeywordPresentInline keyword inline = 
   case inline of 
      Str text                -> (compareWord keyword text)
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
searchBlockListForKeyword :: Text -> PList Block -> Bool 
searchBlockListForKeyword keyword block_list = 
   case block_list of 
      Nil             -> False
      Cons block rst  -> (isKeywordPresentBlock keyword block) || (searchBlockListForKeyword keyword rst) 

-- Seach an Inline list for a particular keyword
searchInlineListForKeyword :: Text -> PList Inline -> Bool
searchInlineListForKeyword keyword inline_list = 
   case inline_list of 
      Nil                -> False 
      Cons inline rst    -> (isKeywordPresentInline keyword inline) || (searchInlineListForKeyword keyword rst)

-- search a blog element for a keyword
searchBlogElementForKeyword :: Text -> BlogElements -> Bool 
searchBlogElementForKeyword keyword element = 
   case element of 
      Header text   -> (compareWord keyword text)
      ID val        -> False 
      Author text   -> False 
      Date   text   -> False
      Content block -> (isKeywordPresentBlock keyword block)
      TagList list  -> False

-- search for a keyword in a blog. 
searchBlogForKeyword :: Text -> Blog -> Bool
searchBlogForKeyword keyword blog = 
   case blog of
      End -> False 
      Next element rst -> (searchBlogElementForKeyword keyword element) || (searchBlogForKeyword keyword rst)

-- search for a keyword in a list of blogs
searchBlogsForKeyword :: Text -> BlogList -> Bool
searchBlogsForKeyword keyword blog_list = 
   case blog_list of 
      None          -> False
      Nxt blog rst  -> (searchBlogForKeyword keyword blog) || (searchBlogsForKeyword keyword rst)


-- main function 
gibbon_main = 
   let blog_list = mkBlogList 100
       keyword :: Text
       keyword = (getRandomString (mod rand 9))
       exists :: Bool 
       some_text :: Text
       some_text = (getRandomString (mod rand 9))
       _        = printsym (quote "NEWLINE")
       _        = printsym (quote "NEWLINE")
       _        = printPacked blog_list
       _        = printsym (quote "NEWLINE")
       _        = printsym (quote "NEWLINE")
       exists   = searchBlogsForKeyword keyword blog_list
       _        = printsym (quote "Does keyword exist in blogs: ")
       _        = printbool exists 
       _        = printsym (quote "NEWLINE")
       _        = printsym (quote "NEWLINE")
       newBlogs = filterBlogsBasedOnTagKeyword keyword blog_list
       _        = printsym (quote "Print the new blogs")
       _        = printsym (quote "NEWLINE")
       _        = printPacked newBlogs
       _        = printsym (quote "NEWLINE")
   in ()
       

-- gibbon --packed --no-gc --toC Main.hs; gcc -g Main.c -o main