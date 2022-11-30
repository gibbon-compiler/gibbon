module Basics where

import Gibbon.Prelude
import Gibbon.PList
import Gibbon.Vector
import Gibbon.Maybe

type Text   = Vector Char

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
        if decimal == 0 then '!'
        else if decimal == 1 then '#'
        else if decimal == 2 then '$'
        else if decimal == 3 then '%'
        else if decimal == 4 then '&'
        else if decimal == 5 then '('
        else if decimal == 6 then ')'
        else if decimal == 7 then '*'
        else if decimal == 8 then '+'
        else if decimal == 9 then ','
        else if decimal == 10 then '-'
        else if decimal == 11 then '.'
        else if decimal == 12 then '/'
        else if decimal == 13 then '0'
        else if decimal == 14 then '1'           
        else if decimal == 15 then '2'
        else if decimal == 16 then '3'
        else if decimal == 17 then '4'
        else if decimal == 18 then '5'
        else if decimal == 19 then '6'
        else if decimal == 20 then '7'
        else if decimal == 21 then '8'
        else if decimal == 22 then '9'
        else if decimal == 23 then ':'
        else if decimal == 24 then ';'
        else if decimal == 25 then '<'
        else if decimal == 26 then '='
        else if decimal == 27 then '>'
        else if decimal == 28 then '?'
        else if decimal == 29 then '@'
        else if decimal == 30 then 'A'
        else if decimal == 31 then 'B'
        else if decimal == 32 then 'C'
        else if decimal == 33 then 'D'
        else if decimal == 34 then 'E'
        else if decimal == 35 then 'F'
        else if decimal == 36 then 'G'
        else if decimal == 37 then 'H'
        else if decimal == 38 then 'I'
        else if decimal == 39 then 'J'
        else if decimal == 40 then 'K'
        else if decimal == 41 then 'L'
        else if decimal == 42 then 'M'
        else if decimal == 43 then 'N'
        else if decimal == 44 then 'O'
        else if decimal == 45 then 'P'
        else if decimal == 46 then 'Q'
        else if decimal == 47 then 'R'
        else if decimal == 48 then 'S'
        else if decimal == 49 then 'T'
        else if decimal == 50 then 'U'
        else if decimal == 51 then 'V'
        else if decimal == 52 then 'W'
        else if decimal == 53 then 'X'
        else if decimal == 54 then 'Y'
        else if decimal == 55 then 'Z'
        else if decimal == 56 then '['
        else if decimal == 57 then ']'
        else if decimal == 58 then '^'
        else if decimal == 59 then '_'
        else if decimal == 60 then '`'
        else if decimal == 61 then 'a'
        else if decimal == 62 then 'b'
        else if decimal == 63 then 'c'
        else if decimal == 64 then 'd'
        else if decimal == 65 then 'e'
        else if decimal == 66 then 'f'
        else if decimal == 67 then 'g'
        else if decimal == 68 then 'h'
        else if decimal == 69 then 'i'
        else if decimal == 70 then 'j'
        else if decimal == 71 then 'k'
        else if decimal == 72 then 'l'
        else if decimal == 73 then 'm'
        else if decimal == 74 then 'n'
        else if decimal == 75 then 'o'
        else if decimal == 76 then 'p'
        else if decimal == 77 then 'q'
        else if decimal == 78 then 'r'
        else if decimal == 79 then 's'
        else if decimal == 80 then 't'
        else if decimal == 81 then 'u'
        else if decimal == 82 then 'v'
        else if decimal == 83 then 'w'
        else if decimal == 84 then 'x'
        else if decimal == 85 then 'y'
        else if decimal == 86 then 'z'
        else if decimal == 87 then '{'
        else if decimal == 88 then '|'
        else if decimal == 89 then '}'
        else '~'

mkChar :: Int -> Char 
mkChar val = getChar (mod rand 91)

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


{- # INLINE # -}
emphasizeBlogContent :: Text -> BlogContent -> Bool -> BlogContent
emphasizeBlogContent keyword oldContent present = case oldContent of 
                                                            Content block -> if (present)
                                                                             then Content (emphasizeKeywordInBlock keyword block)
                                                                             else Content block

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
                                 plist_space :: PList Inline
                                 plist_space = (Cons (Space) plist_inline) 
                                in if (isSpace) then (fileToContent file (singleton (nth file (index+1))) (Cons (Str word) plist_inline) (index+2) max_len)  
                                                else (fileToContent file (append word char_vec) (plist_inline) (index+1) max_len)

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


mkContentFromText :: Text -> BlogContent
mkContentFromText f = 
         let block   = fileToContent f  (singleton (nth f  0)) Nil 1 (vlength f)
             content = mkBlogContent block 
           in content