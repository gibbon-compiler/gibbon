module MeasureMode where

data NodeData = NodeDataK Int Int Int Int Int MeasureMode FontStyle
  deriving Show

data MeasureMode = Flex | Relative | Absolute
  deriving Show

data FontStyle = FontStyleK Int Int Int
  deriving Show

getMeasureMode :: NodeData -> MeasureMode
getMeasureMode node =
  case node of
   NodeDataK posX posY height width relWidth mMode fontStyle -> mMode

gibbon_main =
  let
      font_style = FontStyleK 0 0 0
      node_data  = NodeDataK 0 0 0 0 0 Flex font_style
  in case getMeasureMode node_data of
       Flex -> 42
       Relative -> 0
       Absolute -> -1

main :: IO ()
main = print gibbon_main
