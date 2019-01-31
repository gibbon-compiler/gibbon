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
              | VertContainer HorizContainerList 
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

getHeight :: NodeData -> Int  
getHeight nData  = case (nData) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> height
    
getWidthElement :: Element -> Int  
getWidthElement e  = case (e) of 
    ImageCons a b s nData  -> getWidth nData
    TextBoxCons  a b s nData -> getWidth nData
    VertContainer hzList  -> getMaxWidthHzList hzList
 
getHeightElement :: Element -> Int  
getHeightElement e  = case (e) of 
    ImageCons a b s nData  -> getHeight nData
    TextBoxCons  a b s nData -> getHeight nData
    VertContainer hzList  -> getSumHeights hzList

updateWidth :: NodeData -> Int -> NodeData  
updateWidth nData newWidth = case (nData) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> 
        NodeDataK posX posY height newWidth relWidth mMode fontStyle

updateHeight :: NodeData -> Int -> NodeData  
updateHeight nData newHeight = case (nData) of 
    NodeDataK posX posY height width relWidth mMode fontStyle -> 
        NodeDataK posX posY newHeight width relWidth mMode fontStyle


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

    -- compute width 
-- This traversal compute the width of the page which consists of nested 
-- horizontal and vertical containers with leaf elements, it calls other 
-- traversals (getMaxWidth and sumWidths)

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

resolveWidthElmList :: ElementsList -> ElementsList
resolveWidthElmList elemList  = case (elemList) of 
    ElementsListInner element remList  ->
        ElementsListInner (resolveWidthElm element) 
            (resolveWidthElmList remList) 
    ElementsListEnd element -> 
        ElementsListEnd (resolveWidthElm element) 

resolveWidthElm :: Element -> Element
resolveWidthElm element  = case (element) of 
    VertContainer hzList  -> VertContainer (resolveWidthHzLst hzList) 

gibbon_main =  StrEnd

-- computeWidth a traversal that computes the width of each element 
-- in the render tree this traversal depend on computing the width

computeHeightDoc :: Document -> Document
computeHeightDoc doc = case (doc) of 
    Document pList nData -> Document (computeHeightPList pList) nData 
    
computeHeightPList :: PageList -> PageList
computeHeightPList pList = case (pList) of 
    PageListInner page remList -> PageListInner (computeHeightPage page)
        (computeHeightPList remList)
    PageListEnd page ->PageListEnd ( computeHeightPage page)

getSumHeights :: HorizContainerList -> Int
getSumHeights hzList = case (hzList) of 
    HorizContainerListInner elmList remList -> 
        let maxH = getMaxHeight elmList 
        in addI maxH (getSumHeights remList)
    HorizContainerListEnd elmList -> getMaxHeight elmList 

getMaxHeight :: ElementsList -> Int
getMaxHeight elmList = case (elmList) of 
    ElementsListInner element remList -> 
        let h1 = getMaxHeight remList 
            h2 = getHeightElement element 
        in maxI h1 h2         

computeHeightPage :: Page -> Page
computeHeightPage p = case (p) of
    Page hzList nData -> 
        let hzList'=   computeHeightHzList hzList
        in let newHeight = getSumHeights hzList'
           in Page hzList' (updateHeight nData newHeight )

computeHeightHzList :: HorizContainerList -> HorizContainerList
computeHeightHzList hzList = case (hzList) of 
    HorizContainerListInner elmList remList ->
        let elmList' = computeHeightElmList elmList 
            remList' = computeHeightHzList remList
        in HorizContainerListInner elmList' remList'
    HorizContainerListEnd elmList -> 
        HorizContainerListEnd (computeHeightElmList elmList)

computeHeightElmList :: ElementsList -> ElementsList
computeHeightElmList elmList = case (elmList) of 
    ElementsListInner element remList -> 
        ElementsListInner (computeHeightElement element)
           (computeHeightElmList remList)
    ElementsListEnd element -> ElementsListEnd (computeHeightElement  element)

computeHeightElement :: Element -> Element
computeHeightElement element = case (element) of 
    VertContainer hzList -> VertContainer (computeHeightHzList hzList)

main :: IO ()
main = print gibbon_main
