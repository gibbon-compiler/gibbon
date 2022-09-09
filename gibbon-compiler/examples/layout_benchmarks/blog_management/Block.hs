module Block where

import Inline
--import Format
--import Attribute

data Block =    Plain (Vector Inline)
              | Para (Vector Inline)
              | LineBlock (Vector (Vector Inline))
             -- | CodeBlock Attr Text
             -- | RawBlock Format Text
              | BlockQuote (Vector Block)
             -- | OrderedList ListAttributes [[Block]]
              | BulletList (Vector (Vector Block))
              | DefinitionList (Vector ((Vector Inline) , (Vector (Vector Block))) )
             -- | Header Int Attr (Vector Inline)
              | HorizontalRule
             -- | Table Attr Caption [ColSpec] TableHead [TableBody] TableFoot
             -- | Div Attr (Vector Block)
              | Null
              
              
              
              
              
              
              
              
              
              
              
