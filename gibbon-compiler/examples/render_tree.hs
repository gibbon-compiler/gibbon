module RenderTree where

-- We don't have a built-in Float right now.
data NodeData = NodeDataK Int Int Int Int Int MeasureMode FontStyle
--    NodeDataK posX posY height width relWidth mMode fontStyle

data MeasureMode = Flex | Relative | Absolute
data FontStyle = FontStyleK Int Int Int
data Document = Document PageList NodeData
data PageList = PageListInner Page PageList  
              | PageListEnd Page 
data Page     = Page HorizContainerList NodeData

data HorizContainerList = HorizContainerListInner ElementsList HorizContainerList  
                        | HorizContainerListEnd ElementsList  

data ElementsList  = ElementsListInner  Element ElementsList 
                   | ElementsListEnd Element 
data Element =  ImageCons Int Int StringJ NodeData
              | TextBoxCons Int Int StringJ NodeData
              | VertContainer HorizContainerList NodeData
data StringJ  = StrChar Int
             | StrEnd

maxI :: Int -> Int -> Int
maxI a b = if (a>b) then a else b 

addI :: Int -> Int -> Int 
addI a b = a + b 

getMeasureMode :: NodeData-> MeasureMode
getMeasureMode node  = case (node) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> mMode

getWidth :: NodeData -> Int  
getWidth nData  = case (nData) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> width

getWidthElement :: Element -> Int  
getWidthElement e  = case (e) of 
    ImageCons a b s nData  -> getWidth nData
    TextBoxCons  a b s nData -> getWidth nData
    VertContainer hzList nData -> getWidth nData
 
updateWidth :: NodeData -> Int -> NodeData  
updateWidth nData newWidth = case (nData) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> 
        NodeDataK posX posY height newWidth relWidth mMode fontStyle

-- We might need to rewrite this into two functions .. duh thats alot of work 
-- and maybe performance reduction 
updateWidthIfFlex :: NodeData -> Int -> NodeData  
updateWidthIfFlex nData newWidth = case (nData) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> 
        case (mMode) of
            Flex ->  updateWidth nData newWidth
            Absolute -> nData
            Relative -> nData

getMaxWidthHzList :: HorizContainerList -> Int
getMaxWidthHzList hzList = case (hzList) of
    HorizContainerListInner elmList remList -> 
        maxI (sumWidthsElmList elmList) ( getMaxWidthHzList remList)
    HorizContainerListEnd elmList -> sumWidthsElmList elmList

sumWidthsElmList :: ElementsList -> Int
sumWidthsElmList elmList = case (elmList) of 
    ElementsListInner e remList -> addI (getWidthElement e ) (sumWidthsElmList remList)
    ElementsListEnd e  -> getWidthElement e 
----- 
-- This traversal compute the width of the page which consists of nested 
-- horizontal and vertical containers with leaf elements 
-- TODO : remove the widthMode and assume one mode for that

resolveWidthDoc :: Document -> Document 
resolveWidthDoc doc  = case (doc) of
     Document pgList nData -> Document (resolveWidthPList pgList) nData

resolveWidthPList :: PageList -> PageList 
resolveWidthPList pgList  = case (pgList) of
    PageListInner page remList  ->
        PageListInner (resolveWidthP page) (resolveWidthPList remList) 
    PageListEnd page  -> 
        PageListEnd (resolveWidthP page) 

-- This is different than treefuser implementation where maxWidth was explicitly 
-- computing maxWidth during resolveWidth and store it on the stack .
-- we hope that tupling would that for us here.
resolveWidthP :: Page -> Page
resolveWidthP p  = case (p) of
    Page hzList nData-> 
        let  hzList' = resolveWidthHzLst hzList 
         in let maxWidth = getMaxWidthHzList hzList' 
            in let nData' = updateWidthIfFlex nData maxWidth    
               in Page hzList' nData'

resolveWidthHzLst :: HorizContainerList -> HorizContainerList
resolveWidthHzLst hzList  = case (hzList) of 
    HorizContainerListInner  elmList remList ->
        HorizContainerListInner (resolveWidthElmList elmList)  
           (resolveWidthHzLst remList) 
    HorizContainerListEnd elmList -> 
        HorizContainerListEnd (resolveWidthElmList elmList) 

resolveWidthElmList ::ElementsList -> ElementsList
resolveWidthElmList elemList  = case (elemList) of 
    ElementsListInner element remList  ->
        ElementsListInner (resolveWidthElm element) 
            (resolveWidthElmList remList) 
    ElementsListEnd element -> 
        ElementsListEnd (resolveWidthElm element) 

resolveWidthElm ::Element -> Element
resolveWidthElm element  = case (element) of 
    VertContainer hzList nData -> VertContainer (resolveWidthHzLst hzList) nData

gibbon_main =  StrEnd

main :: IO ()
main = print gibbon_main
