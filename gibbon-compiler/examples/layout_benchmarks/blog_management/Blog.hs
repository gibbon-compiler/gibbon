module Blog where

import Text
import Block


data Blog =   Header Text
            | Author Text
            | Date   Text
            | Content Block
            | TagList (Vector Text)
        --  | Parent   (Vector Blog)
        --  | Children (Vector Blog)
        --  | YPos Float
        --  | Xpos Float
        --  | Width Float
        --  | Height Float
        
