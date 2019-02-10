module RenderTree where

-- We don't have a built-in Float right now.
data NodeData = NodeDataK Int Int Int Int Int  FontStyle
--    NodeDataK posX posY height width relWidth mMode fontStyle

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


getWidth :: NodeData -> Int  
getWidth nData  = case (nData) of 
    NodeDataK posX posY height width relWidth  fontStyle -> width

getHeight :: NodeData -> Int  
getHeight nData  = case (nData) of 
    NodeDataK posX posY height width relWidth  fontStyle -> height
    
getWidthElement :: Element -> Int  
getWidthElement e  = case (e) of 
    ImageCons a b s nData  -> getWidth nData
    TextBoxCons  a b s nData -> getWidth nData
    VertContainer hzList x -> getMaxWidthHzList hzList
 
getHeightElement :: Element -> Int  
getHeightElement e  = case (e) of 
    ImageCons a b s nData  -> getHeight nData
    TextBoxCons  a b s nData -> getHeight nData
    VertContainer hzList  x-> getSumHeights hzList

updateWidth :: NodeData -> Int -> NodeData  
updateWidth nData newWidth = case (nData) of 
    NodeDataK posX posY height width relWidth  fontStyle -> 
        NodeDataK posX posY height newWidth relWidth  fontStyle

updateHeight :: NodeData -> Int -> NodeData  
updateHeight nData newHeight = case (nData) of 
    NodeDataK posX posY height width relWidth  fontStyle -> 
        NodeDataK posX posY newHeight width relWidth  fontStyle

-- We might need to rewrite this into two functions .. duh thats alot of work 
-- and maybe performance reduction 
-- updateWidthIfFlex :: NodeData -> Int -> NodeData  
-- updateWidthIfFlex nData newWidth = case (nData) of 
--     NodeDataK posX posY height width relWidth mMode fontStyle -> 
--         case (mMode) of
--             Flex ->  updateWidth nData newWidth
--             Absolute -> nData
--             Relative -> nData

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
            in let nData' = updateWidth nData maxWidth    
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
    VertContainer hzList  nData-> 
        let  hzList' = resolveWidthHzLst hzList 
        in let maxWidth = getMaxWidthHzList hzList' 
           in let nData' = updateWidth nData maxWidth    
              in VertContainer hzList' nData' 
    ImageCons a b c d ->   ImageCons a b c d
    TextBoxCons a b c d ->TextBoxCons a b c d

gibbon_main = computeHeightElement( resolveWidthElm  (
     TextBoxCons 1 1 StrEnd (NodeDataK 1 1 1 1 1  (FontStyleK 1 1 1))))


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
    ElementsListEnd element -> 
        getHeightElement element      

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
    VertContainer hzList nData->   
        let hzList'=   computeHeightHzList hzList
          in let newHeight = getSumHeights hzList'
            in   VertContainer  hzList' (updateHeight nData newHeight )

    ImageCons a b c d ->   ImageCons a b c d
    TextBoxCons a b c d ->TextBoxCons a b c d


main :: IO ()
main = 
    do
      let d = (NodeDataK 1 1 1 1 1  (FontStyleK 1 1 1))
      let input = TextBoxCons 1 1 StrEnd d
      let x = computeHeightElement( resolveWidthElm  (input))
      return $ print x
