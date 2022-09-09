module Inline where

import Text
import Target
--import Attribute
--import Block

data Inline =   Str Text
              | Emph (Vector Inline)
              | Underline (Vector Inline)
              | Strong (Vector Inline)
              | Strikeout (Vector Inline)
              | Superscript (Vector Inline)
              | Subscript (Vector Inline)
              | SmallCaps (Vector Inline)
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
             -- | Note (Vector Block)
             -- | Span Attr (Vector Inline)

