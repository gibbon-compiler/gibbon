module Basics where

import Gibbon.Prelude
import Gibbon.PList
import Gibbon.Vector
--import Gibbon.Maybe

type Text   = Vector Char

type TextList = Vector Text

--type Target = (Text, Text)
--type Attr   = (Text, (PList Text), (PList (Text, Text)))
--type Format = Format Text

-- For simplicity, we are assuming for this benchmark that data Inline is tokenized at the "word" level.
-- Therefore, The Base case where "Text" is used is going to be a single word, i.e, "Str Text".
data Inline =     Str Text
                | Emph (PList Inline)
             -- | Underline (PList Inline)
             -- | Strong (PList Inline)
             -- | Strikeout (PList Inline)
             -- | Superscript (PList Inline)
             -- | Subscript (PList Inline)
             -- | SmallCaps (PList Inline)
             -- | Quoted QuoteType (PList Inline)
             -- | Cite [Citation] (PList Inline)
             -- | Code Attr Text
                | Space
             -- | SoftBreak
             -- | LineBreak
             -- | Math MathType Text
             -- | RawInline Format Text
             -- | Link Attr (PList Inline) Target
             -- | Image Attr (PList Inline) Target
             -- | Note (PList Block)
             -- | Span Attr (PList Inline)
                deriving (Show)  

data Block =      Plain (PList Inline)
             -- | Para  (PList Inline)
             -- | LineBlock (PList (PList Inline))
             -- | CodeBlock Attr Text
             -- | RawBlock Format Text
             -- | BlockQuote (PList Block)
             -- | OrderedList ListAttributes [[Block]]
             -- | BulletList (PList (PList Block))
             -- | DefinitionList PList ( PList Inline , PList (PList Block) ) ---> This is resulting in a compile time error (TODO: DEBUG)
             -- | Header Int Attr (PList Inline)
             -- | HorizontalRule
             -- | Table Attr Caption [ColSpec] TableHead [TableBody] TableFoot
             -- | Div Attr (PList Block)
                | Null
                deriving (Show)

-- Define Blog elements
data BlogHeader  = Header Text
data BlogId      = ID Int
data BlogAuthor  = Author Text
data BlogDate    = Date Text
data BlogContent = Content Block
data BlogTags    = TagList (PList Text)

-- Define packed Blog data Type/s, we can arrange the fields here to change their relative ordering. 
data Blog =   End 
            | Layout1 (BlogHeader) (BlogId) (BlogAuthor) (BlogDate) (BlogContent) (BlogTags) (Blog)
            | Layout2 (BlogContent) (BlogTags) (Blog) (BlogHeader) (BlogId) (BlogAuthor) (BlogDate) 
            | Layout3 (BlogTags) (Blog) (BlogContent) (BlogHeader) (BlogId) (BlogAuthor) (BlogDate)
            | Layout4 (BlogTags) (BlogContent) (Blog) (BlogHeader) (BlogId) (BlogAuthor) (BlogDate)
            | Layout5 (Blog) (BlogTags) (BlogContent) (BlogHeader) (BlogId) (BlogAuthor) (BlogDate)
            | Layout6 (BlogHeader) (BlogId) (BlogAuthor) (BlogDate) (BlogContent) (Blog) (BlogTags)
            | Layout7 (Blog) (BlogContent) (BlogHeader) (BlogId) (BlogAuthor) (BlogDate) (BlogTags)
            | Layout8 (BlogContent) (Blog) (BlogId) (BlogAuthor) (BlogDate) (BlogHeader) (BlogTags)
            deriving (Show)


getChar :: Int -> Char
getChar decimal =  
        --if decimal == 0 then '!'
        --else if decimal == 1 then '#'
        --else if decimal == 2 then '$'
        --else if decimal == 3 then '%'
        --else if decimal == 4 then '&'
        --else if decimal == 5 then '('
        --else if decimal == 6 then ')'
        --else if decimal == 7 then '*'
        --else if decimal == 8 then '+'
        --else if decimal == 9 then ','
        --else if decimal == 10 then '-'
        --else if decimal == 11 then '.'
        --else if decimal == 12 then '/'
        --else if decimal == 13 then '0'
        --else if decimal == 14 then '1'           
        --else if decimal == 15 then '2'
        --else if decimal == 16 then '3'
        --else if decimal == 17 then '4'
        --else if decimal == 18 then '5'
        --else if decimal == 19 then '6'
        --else if decimal == 20 then '7'
        --else if decimal == 21 then '8'
        --else if decimal == 22 then '9'
        --else if decimal == 23 then ':'
        --else if decimal == 24 then ';'
        --else if decimal == 25 then '<'
        --else if decimal == 26 then '='
        --else if decimal == 27 then '>'
        --else if decimal == 28 then '?'
        --else if decimal == 29 then '@'
        --else if decimal == 30 then 'A'
        --else if decimal == 31 then 'B'
        --else if decimal == 32 then 'C'
        --else if decimal == 33 then 'D'
        --else if decimal == 34 then 'E'
        --else if decimal == 35 then 'F'
        --else if decimal == 36 then 'G'
        --else if decimal == 37 then 'H'
        --else if decimal == 38 then 'I'
        --else if decimal == 39 then 'J'
        --else if decimal == 40 then 'K'
        --else if decimal == 41 then 'L'
        ---else if decimal == 42 then 'M'
        --else if decimal == 43 then 'N'
        --else if decimal == 44 then 'O'
        --else if decimal == 45 then 'P'
        --else if decimal == 46 then 'Q'
        --else if decimal == 47 then 'R'
        --else if decimal == 48 then 'S'
        --else if decimal == 49 then 'T'
        --else if decimal == 50 then 'U'
        --else if decimal == 51 then 'V'
        --else if decimal == 52 then 'W'
        --else if decimal == 53 then 'X'
        --else if decimal == 54 then 'Y'
        --else if decimal == 55 then 'Z'
        --else if decimal == 56 then '['
        --else if decimal == 57 then ']'
        --else if decimal == 58 then '^'
        --else if decimal == 59 then '_'
        --else if decimal == 60 then '`'
        if decimal == 0 then 'a'
        --else if decimal == 61 then 'a'
        else if decimal == 1 then 'b'
        else if decimal == 2 then 'c'
        else if decimal == 3 then 'd'
        else if decimal == 4 then 'e'
        else if decimal == 5 then 'f'
        else if decimal == 6 then 'g'
        else if decimal == 7 then 'h'
        else if decimal == 8 then 'i'
        else if decimal == 9 then 'j'
        else if decimal == 10 then 'k'
        else if decimal == 11 then 'l'
        else if decimal == 12 then 'm'
        else if decimal == 13 then 'n'
        else if decimal == 14 then 'o'
        else if decimal == 15 then 'p'
        else if decimal == 16 then 'q'
        else if decimal == 17 then 'r'
        else if decimal == 18 then 's'
        else if decimal == 19 then 't'
        else if decimal == 20 then 'u'
        else if decimal == 21 then 'v'
        else if decimal == 22 then 'w'
        else if decimal == 23 then 'x'
        else if decimal == 24 then 'y'
        --else if decimal == 86 then 'z'
        else 'z'
        --else if decimal == 87 then '{'
        --else if decimal == 88 then '|'
        --else if decimal == 89 then '}'
        --else '~'

mkChar :: Int -> Char 
mkChar val = getChar (mod rand 26)

-- Get a random word, Int is the length of the string.
-- Based on internet, average english word is 5 characters long
getRandomString :: Int -> Text 
getRandomString length = generate length mkChar

-- Utility Functions to make Blogs and its Elements.
mkBlogHeader :: Text -> BlogHeader
mkBlogHeader text = Header text 

mkBlogID :: Int -> BlogId 
mkBlogID val = ID val 

mkBlogAuthor :: Text -> BlogAuthor 
mkBlogAuthor text = Author text

mkBlogDate :: Text -> BlogDate 
mkBlogDate text = Date text 

mkBlogContent :: Block -> BlogContent 
mkBlogContent block = Content block 

mkBlogTags :: (PList Text) -> BlogTags 
mkBlogTags taglist = TagList taglist       


getFile :: Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> Int -> Text 
getFile f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 select = 
   if (select == 0) then f1
   else if (select == 1) then f2 
   else if (select == 2) then f3 
   else if (select == 3) then f4 
   else if (select == 4) then f5 
   else if (select == 5) then f6
   else if (select == 6) then f7
   else if (select == 7) then f8
   else if (select == 8) then f9 
   else f10


mkListFiles :: Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> Int -> PList Text
mkListFiles f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len = if len < 0 then Nil 
                                                         else 
                                                            let f   = (getFile f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len)
                                                                rst = (mkListFiles f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (len - 1))
                                                              in Cons f rst


checkBlogID :: BlogId -> Int -> Bool
checkBlogID id val = case id of 
                        ID x -> if ( x == val ) then True 
                                                else False

-- Function to compare two words, each represented by Vector Char. 
compareWord :: Text -> Text -> Bool
compareWord word1 word2 = 
   let len1        = length word1 
       len2        = length word2
       compare_len = if (len1 == len2) then True else False     
   in if (compare_len) then (cmp 0 len1 word1 word2) else False

-- Compare 2 Vector Char (Text) or words for equality if their length is the same. 
cmp :: Int -> Int -> Vector Char -> Vector Char -> Bool
cmp start end word1 word2 =
   if (start < end) then 
      let a       = nth word1 start
          b       = nth word2 start
          eq      = if (a *==* b) then True else False 
          recurse = cmp (start+1) end word1 word2
         in (eq && recurse) 
   else True

-- Search a TagList (PList Text) for some keyword
searchTagList :: Text -> PList Text -> Bool 
{-# INLINE searchTagList #-}
searchTagList keyword taglist = case taglist of 
   Nil -> False 
   Cons word rst -> (compareWord keyword word) || (searchTagList keyword rst) 

-- delete a keyword in a TagList
deleteTagList :: Text -> PList Text -> PList Text 
deleteTagList keyword taglist = case taglist of 
   Nil -> Nil 
   Cons word rst -> if (compareWord keyword word) then (deleteTagList keyword rst) 
                    else Cons word (deleteTagList keyword rst)


insertTagList :: Text -> PList Text -> PList Text 
insertTagList keyword taglist = case taglist of 
   Nil -> (Cons keyword) Nil
   Cons word rst -> insertTagList keyword rst

-- Tell if a particular keyword exists in a Block data type or not
isKeywordPresentInBlock :: Text -> Block -> Bool
isKeywordPresentInBlock keyword contentBlock = 
   case contentBlock of 
      Plain list_inline      -> (searchInlineListForKeyword keyword list_inline)
      --Para  list_inline      -> (searchInlineListForKeyword keyword list_inline)
      --BlockQuote list_block  -> (searchBlockListForKeyword keyword list_block)
      --HorizontalRule         -> False
      Null                   -> False 

-- Tell if a particular keyword exists in an inline data type or not. (search a Inline)
isKeywordPresentInline :: Text -> Inline -> Bool
isKeywordPresentInline keyword inline = 
   case inline of 
      Str text                -> (compareWord keyword text)
      Emph list_inline        -> (searchInlineListForKeyword keyword list_inline)
      --Underline list_inline   -> (searchInlineListForKeyword keyword list_inline)
      --Strong list_inline      -> (searchInlineListForKeyword keyword list_inline)
      --Strikeout list_inline   -> (searchInlineListForKeyword keyword list_inline)
      --Superscript list_inline -> (searchInlineListForKeyword keyword list_inline)
      --Subscript list_inline   -> (searchInlineListForKeyword keyword list_inline) 
      --SmallCaps list_inline   -> (searchInlineListForKeyword keyword list_inline) 
      Space                   -> False
      --SoftBreak               -> False 
      --LineBreak               -> False 
      --Note list_block         -> (searchBlockListForKeyword keyword list_block)

-- Search a block list for a particular keyword
searchBlockListForKeyword :: Text -> PList Block -> Bool 
searchBlockListForKeyword keyword block_list = 
   case block_list of 
      Nil             -> False
      Cons block rst  -> (isKeywordPresentInBlock keyword block) || (searchBlockListForKeyword keyword rst) 

-- Search an Inline list for a particular keyword
searchInlineListForKeyword :: Text -> PList Inline -> Bool
searchInlineListForKeyword keyword inline_list = 
   case inline_list of 
      Nil                -> False 
      Cons inline rst    -> (isKeywordPresentInline keyword inline) || (searchInlineListForKeyword keyword rst)

-- Emphasize a particular keyword in a Block type
emphasizeKeywordInBlock :: Text -> Block -> Block
emphasizeKeywordInBlock keyword contentBlock = 
   case contentBlock of 
      Plain list_inline      -> Plain (emphasizeInlineListForKeyword keyword list_inline)
      --Para  list_inline      -> Para  (emphasizeInlineListForKeyword keyword list_inline)
      --BlockQuote list_block  -> BlockQuote (emphasizeKeywordInBlockList keyword list_block)
      --HorizontalRule         -> HorizontalRule
      Null                   -> Null

-- Emphasize a particular keyword in an Inline data type
emphasizeKeywordInline :: Text -> Inline -> Inline 
emphasizeKeywordInline keyword inline = 
   case inline of 
      Str text           -> let isSame = compareWord keyword text 
                                --_ = printsym (quote "NEWLINE")
                                --_       = printbool isSame
                                --_ = printsym (quote "NEWLINE")
                                in if (isSame) then let
                                       newlist :: PList Inline 
                                       newlist = (Cons (copyPacked inline)) Nil                         -- ---> Here we had to use a call to copyPacked in order to copy over the inline to a new region, otherwise segfaults. 
                                    in (Emph newlist)
                                   else inline
      Emph list_inline        -> Emph (emphasizeInlineListForKeyword keyword list_inline)
      --Underline list_inline   -> Underline (emphasizeInlineListForKeyword keyword list_inline)
      --Strong list_inline      -> Strong (emphasizeInlineListForKeyword keyword list_inline)
      --Strikeout list_inline   -> Strikeout (emphasizeInlineListForKeyword keyword list_inline)
      --Superscript list_inline -> Superscript (emphasizeInlineListForKeyword keyword list_inline)
      --Subscript list_inline   -> Subscript (emphasizeInlineListForKeyword keyword list_inline) 
      --SmallCaps list_inline   -> SmallCaps (emphasizeInlineListForKeyword keyword list_inline) 
      Space                   -> Space
      --SoftBreak               -> SoftBreak 
      --LineBreak               -> LineBreak 
      --Note list_block         -> Note (emphasizeKeywordInBlockList keyword list_block) 

-- Emphasize a particular keyword in an Inline list
emphasizeInlineListForKeyword :: Text -> PList Inline -> PList Inline
{-# INLINE emphasizeInlineListForKeyword #-}
emphasizeInlineListForKeyword keyword inline_list = 
   case inline_list of 
      Nil                -> Nil 
      Cons inline rst    -> let 
                             newinline = emphasizeKeywordInline keyword inline
                             rst'      = emphasizeInlineListForKeyword keyword rst  
                             in Cons newinline rst'

-- Emphasize a particular keyword in a block list
emphasizeKeywordInBlockList :: Text -> PList Block -> PList Block 
emphasizeKeywordInBlockList keyword block_list = 
   case block_list of 
      Nil             -> Nil
      Cons block rst  -> let
                           newBlock = emphasizeKeywordInBlock keyword block 
                           rst'     = emphasizeKeywordInBlockList keyword rst 
                           in Cons newBlock rst'
                           

searchBlogTags :: Text -> BlogTags -> Bool 
searchBlogTags keyword tags = case tags of 
   TagList list -> searchTagList keyword list


deleteBlogTags :: Text -> BlogTags -> BlogTags
deleteBlogTags keyword tags = case tags of 
   TagList list -> TagList (deleteTagList keyword list)

insertBlogTags :: Text -> BlogTags -> BlogTags 
insertBlogTags keyword tags = case tags of 
   TagList list -> TagList (insertTagList keyword list)

-- emphasize blog content, if present is True
emphasizeBlogContent' :: Text -> BlogContent -> BlogContent
emphasizeBlogContent' keyword oldContent = case oldContent of 
                                                Content block -> Content (emphasizeKeywordInBlock keyword block)



emphasizeBlogContent :: Text -> BlogContent -> BlogContent
emphasizeBlogContent keyword oldContent = case oldContent of 
                                             Content block -> Content (emphasizeKeywordInBlock keyword block)

searchBlogContent :: Text -> BlogContent -> Bool 
searchBlogContent keyword content = case content of 
      Content block -> (isKeywordPresentInBlock keyword block)
                    

fileToContent :: Vector Char -> Vector Char -> PList Inline -> Int -> Int -> Block
fileToContent file word plist_inline index max_len = 
      if index >= max_len then (Plain plist_inline)                                                                     
                           else let 
                                 character :: Char
                                 character    = nth file index
                                 isSpace      = if ( character *==* (head " ") ) then True else False
                                 char_vec     = (singleton character)
                                 --plist_space :: PList Inline
                                 --plist_space = (Cons (Space) plist_inline) 
                                in if (isSpace) then (fileToContent file (singleton (nth file (index+1))) (Cons (Str word) plist_inline) (index+2) max_len)  
                                                else (fileToContent file (append word char_vec) (plist_inline) (index+1) max_len)


fileToContent' :: Vector Char -> Vector Char -> TextList -> Int -> Int -> TextList
fileToContent' file word running_list index max_len = 
      if index >= max_len then (append running_list (valloc 0) )    --(generate 1 (\i -> ""))                                                                 
                           else let 
                                 character :: Char
                                 character    = nth file index
                                 isSpace      = if ( character *==* (head " ") ) then True else False
                                 char_vec     = (singleton character)
                                in if (isSpace) then (fileToContent' file (singleton (nth file (index+1))) (append running_list (generate 1 (\i -> word))) (index+2) max_len)  
                                                else (fileToContent' file (append word char_vec) (running_list) (index+1) max_len)

printWordList :: TextList -> Int -> Int -> ()
printWordList vec start end = if start < end then
                                 let 
                                    element = nth vec start
                                    _   = printVec (\i -> printchar i) element
                                  in printWordList vec (start+1) end
                              else ()  


fileToTags :: Vector Char -> Vector Char -> Int -> Int -> PList Text 
fileToTags file word index max_len = 
   if index >= max_len then Nil
                       else let 
                              character :: Char 
                              character = nth file index 
                              isSpace = if ( character *==* (head " ") ) then True else False
                              char_vec = (singleton character)   
                             in if (isSpace) then Cons word (fileToTags file (singleton (nth file (index+1))) (index+2) max_len)
                                             else (fileToTags file (append word char_vec) (index+1) max_len)       


mkTagsFromText :: Text -> BlogTags
mkTagsFromText f' =
       let tags  = fileToTags f' (singleton (nth f' 0)) 1 (vlength f')
           tags' = TagList tags 
         in tags' 


{- # INLINE # -}
mkContentFromText :: Text -> BlogContent
mkContentFromText f = 
         let block   = fileToContent f  (singleton (nth f  0)) Nil 1 (vlength f)
             content = mkBlogContent block 
           in content

-- Make an Inline type, option chooses what kind of Inline data type we are creating
-- This creates all the base cases for the inline type 
mkInlineBaseCase :: Int -> Inline
mkInlineBaseCase option = 
   if option == 0 then (Str (getRandomString 5))   -- get a random word
   else Space 

-- Make a list of Inline data Type.
mkInlineList :: Int -> Int -> (PList Inline)
mkInlineList length base = 
   if length <= 0 then Nil 
   -- If its not base case, then don't stop recursion. 
   else if (base == 0) then 
      let item = Emph (mkInlineList 100 1)
          rst  = (mkInlineList (length - 1) base)
          in Cons item rst
   -- If its  base case, then stop recursion in Inline data type and only add base cases. 
   else let item = (mkInlineBaseCase (mod rand 4))
            rst  = mkInlineList (length - 1) base 
         in Cons item rst

-- Make a list of Inline data Type.
mkInlineList' :: Int -> Int -> TextList -> (PList Inline)
mkInlineList' length index words = 
   if index >= length then Nil  
   else let item = Str (nth words index)
            rst  = mkInlineList' length (index+1) words 
         in Cons item rst

mkRandomInlineList :: Int -> (PList Inline)
mkRandomInlineList len = if len <= 0 then Nil 
                         else let word = Str (getRandomString 1)
                                  rst  = mkRandomInlineList (len - 1) 
                                in Cons word rst

mkSomeTags :: Int -> PList Text
mkSomeTags len = if len <= 0 then Nil 
                 else let word = "a" --(getRandomString 1)
                          rst  = mkSomeTags (len - 1)
                       in Cons word rst


-- Make a list of blocks
mkBlockList :: Int -> Int -> (PList Block)
mkBlockList length base = 
   if length <= 0 then Nil
   else if (base == 0) then
      let item = (Plain (mkInlineList 1000 1))
          rst  = (mkBlockList (length - 1) base)
      in Cons item rst
   else let item = Null
            rst  = (mkBlockList (length - 1) base) 
      in Cons item rst

-- Make a Block data type with random data, make depth of recursion to 1 for now
-- mkBlock :: Int -> Block
-- mkBlock option = 
--    if option == 0 then (Plain (mkInlineList 1000 1))
--    else if option == 1 then (Para (mkInlineList 1000 1))
--    else (BlockQuote (mkBlockList 1000 1))

-- -- Base case for make Block
-- mkBlockBaseCase :: Int -> Block 
-- mkBlockBaseCase option = 
--    if option == 0 then HorizontalRule
--    else Null

-- Make an Inline type, option chooses what kind of Inline data type we are creating
-- This will Purposefully make Inline lists at a depth of recursion 1, this can be modified to increase the depth of recursion.
-- This function crates the recursive fields. 
-- mkInline :: Int -> Inline
-- mkInline option = 
--    if option == 0 then (Emph (mkInlineList 100 1))
--    else if option == 1 then (Underline (mkInlineList 100 1))
--    else if option == 2 then (Strong (mkInlineList 100 1))
--    else if option == 3 then (Strikeout (mkInlineList 100 1))
--    else if option == 4 then (Superscript (mkInlineList 100 1))
--    else if option == 5 then (Subscript (mkInlineList 100 1))
--    else if option == 6 then (SmallCaps (mkInlineList 100 1))
--    else (Note (mkBlockList 100 1))


blogLength :: Blog -> Int
blogLength blog = case blog of
                        End -> 0
                        Layout1 a b c d e f rst  -> 1 + blogLength rst
                        Layout2 a b rst c d e f  -> 1 + blogLength rst
                        Layout3 a rst b c d e f  -> 1 + blogLength rst
                        Layout4 a b rst d e f g  -> 1 + blogLength rst
                        Layout5 rst a b c d e f  -> 1 + blogLength rst
                        Layout6 a b c d e rst f  -> 1 + blogLength rst
                        Layout7 rst a b c d e f  -> 1 + blogLength rst
                        Layout8 a rst b c d e f  -> 1 + blogLength rst


printContent :: BlogContent -> ()
printContent content = 
    case content of 
        Content block -> 
            let _ = printsym (quote "Content ")
                _ = printBlock block
            in () 

printTagList :: BlogTags -> ()
printTagList tags = 
    case tags of 
        TagList plist -> 
            let _ = printsym (quote "TagList ")
                _ = printPlistText plist
            in ()
            
printDate :: BlogDate -> () 
printDate date = case date of 
                     Date str -> let _ = printsym (quote "Date ")
                                     _ = printVec (\i -> printchar i) str
                                  in ()

printAuthor :: BlogAuthor -> () 
printAuthor date = case date of 
                     Author str -> let _ = printsym (quote "Author ")
                                       _ = printVec (\i -> printchar i) str
                                    in ()

printHeader :: BlogHeader -> () 
printHeader header = case header of 
                          Header str -> let _ = printsym (quote "Header ")
                                            _ = printVec (\i -> printchar i) str
                                         in ()

printID :: BlogId -> () 
printID id = case id of 
                     ID val -> let _ = printsym (quote "ID ")
                                   _ = printint val
                                in ()

printBlog :: Blog -> () 
printBlog blog = case blog of 
                    Layout1 header id author date content tags rst -> let _ = printsym (quote "Layout1 ")
                                                                          _ = printHeader header
                                                                          _ = printID id 
                                                                          _ = printAuthor author 
                                                                          _ = printDate date 
                                                                          _ = printContent content 
                                                                          _ = printTagList tags
                                                                          _ = printBlog rst
                                                                       in ()



printBlock :: Block -> ()
printBlock block = case block of 
                       Plain plist -> let _ = printsym (quote "Plain ")
                                          _ = printPlistInline plist
                                       in ()
                       Null -> let _ = printsym (quote "Null")
                                in ()

printPlistInline :: PList Inline -> ()
printPlistInline list = case list of 
                     Cons x rst ->  let _ = printsym (quote "PList ( Cons ")
                                        _ = printInline x
                                        _ = printPlistInline rst
                                        _ = printsym (quote " ) ")
                                     in ()
                     Nil  ->  let _ = printsym (quote "Nil")
                               in ()

printPlistText :: PList Text -> ()
printPlistText list = case list of 
                     Cons x rst ->  let _ = printsym (quote "PList ( Cons ")
                                        _ = printVec (\i -> printchar i) x
                                        _ = printPlistText rst
                                        _ = printsym (quote " ) ")
                                     in ()
                     Nil  ->  let _ = printsym (quote "Nil")
                               in ()

printInline :: Inline -> () 
printInline inline = case inline of 
                            Str text -> let _ = printsym (quote "Str ")
                                            _ = printVec (\i -> printchar i) text
                                         in ()
                            Emph plist -> let _ = printsym (quote "Emph ")
                                              _ = printPlistInline plist
                                           in () 
                            Space -> let _ = printsym (quote "Space ")
                                       in ()
