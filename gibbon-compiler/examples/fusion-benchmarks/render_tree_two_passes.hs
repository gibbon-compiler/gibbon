module RenderTree where

-- We don't have a built-in Float right now.
data DisplayData = DisplayDataK Int Int Int Int FontStyle
--DisplayDataK posX posY height width fontStyle

data FontStyle = FontStyleK Int Int Int
-- FontStyleK size fontType color

data Document = Document PageList

data PageList = PageListInner Page PageList
              | PageListEnd Page

data Page     = Page HorizContainerList DisplayData

data HorizContainerList = HorizContainerListInner HrzContainer HorizContainerList
                        | HorizContainerListEnd HrzContainer

data HrzContainer = HrzContainer ElementsList DisplayData

data ElementsList  = ElementsListInner  Element ElementsList
                   | ElementsListEnd Element

data Element =  ImageCons Int Int StringJ DisplayData
              | TextBoxCons Int  StringJ DisplayData
              | VertContainer HorizContainerList DisplayData

data StringJ  = StrChar Int StringJ
              | StrEnd


-- Those functions are basic that sets/gets a field
getStrLength :: StringJ -> Int
getStrLength str = case str of
  StrEnd -> 1
  StrChar char rem -> 1 + (getStrLength rem)

maxI :: Int -> Int -> Int
maxI a b = if (a>b) then a else b

addI :: Int -> Int -> Int
addI a b = a + b

getDisplayDataOfHrzContainer :: HrzContainer -> DisplayData
getDisplayDataOfHrzContainer container = case (container) of
    HrzContainer elmList displayData -> displayData

getDisplayDataOfElement :: Element -> DisplayData
getDisplayDataOfElement element = case (element) of
    ImageCons imgWFixed ratio imgUrl displayData -> displayData
    TextBoxCons  txtWFixed txtContent displayData -> displayData
    VertContainer hzList displayData -> displayData

getDisplayWidth :: DisplayData -> Int
getDisplayWidth displayData  = case (displayData) of
    DisplayDataK posX posY height width fontStyle -> width

getDisplayHeight :: DisplayData -> Int
getDisplayHeight displayData  = case (displayData) of
    DisplayDataK posX posY height width fontStyle -> height

setDisplayWidth :: DisplayData -> Int -> DisplayData
setDisplayWidth displayData newWidth = case (displayData) of
    DisplayDataK posX posY height width fontStyle ->
        DisplayDataK posX posY height newWidth fontStyle

setDisplayHeight :: DisplayData -> Int -> DisplayData
setDisplayHeight displayData newHeight = case (displayData) of
    DisplayDataK posX posY height width fontStyle ->
        DisplayDataK posX posY newHeight width fontStyle

setDisplayPosX :: DisplayData -> Int -> DisplayData
setDisplayPosX displayData x = case (displayData) of
    DisplayDataK posX posY height width fontStyle ->
        DisplayDataK x posY height width fontStyle

setDisplayPosY :: DisplayData -> Int -> DisplayData
setDisplayPosY displayData y = case (displayData) of
    DisplayDataK posX posY height width fontStyle ->
        DisplayDataK posX y height width fontStyle

-- end of basic functions

-- helper functions ends
-- ** computeDisplayWidth traversal**
-- A traversal that computes the width of each visible element in the render tree
-- and updates displayData accordingly
computeDisplayWidthDoc :: Document -> Document
computeDisplayWidthDoc doc  = case (doc) of
     Document pgList  -> Document (computeDisplayWidthPList pgList)

computeDisplayWidthPList :: PageList -> PageList
computeDisplayWidthPList pgList  = case (pgList) of
    PageListInner page remList  ->
        PageListInner (computeDisplayWidthP page) (computeDisplayWidthPList remList)
    PageListEnd page  ->
        PageListEnd (computeDisplayWidthP page)

computeDisplayWidthP :: Page -> Page
computeDisplayWidthP p  = case (p) of
    Page hzList displayData->
        let  hzList' = computeDisplayWidthHzLst hzList
         in let maxWidth = getMaxDisplayWidth hzList'
            in let displayData' = setDisplayWidth displayData maxWidth
               in Page hzList' displayData'

computeDisplayWidthHzLst :: HorizContainerList -> HorizContainerList
computeDisplayWidthHzLst hzList  = case (hzList) of
    HorizContainerListInner  hzContainer remList ->
        HorizContainerListInner (computeDisplayWidthHzContainer hzContainer)
           (computeDisplayWidthHzLst remList)
    HorizContainerListEnd hzContainer ->
        HorizContainerListEnd (computeDisplayWidthHzContainer hzContainer)

computeDisplayWidthHzContainer :: HrzContainer -> HrzContainer
computeDisplayWidthHzContainer container = case (container) of
    HrzContainer elmList displayData ->
        let elmList'  = computeDisplayWidthElmList elmList in
        let sumWidths = sumDisplayWidths elmList' in
        HrzContainer (elmList') (setDisplayWidth displayData sumWidths)

computeDisplayWidthElmList :: ElementsList -> ElementsList
computeDisplayWidthElmList elemList  = case (elemList) of
    ElementsListInner element remList  ->
        ElementsListInner (computeDisplayWidthElm element)
            (computeDisplayWidthElmList remList)
    ElementsListEnd element ->
        ElementsListEnd (computeDisplayWidthElm element)

computeDisplayWidthElm :: Element -> Element
computeDisplayWidthElm element  = case (element) of
    VertContainer hzList  displayData->
        let hzList' = computeDisplayWidthHzLst hzList in
        let maxWidth = getMaxDisplayWidth hzList' in
        let displayData' = setDisplayWidth displayData maxWidth   in
        VertContainer hzList' displayData'
    ImageCons imgWFixed ratio imgUrl displayData  ->
        ImageCons imgWFixed ratio imgUrl (setDisplayWidth displayData imgWFixed)
    TextBoxCons txtWFixed txtContent displayData  ->
     TextBoxCons txtWFixed txtContent (setDisplayWidth displayData txtWFixed)

sumDisplayWidths :: ElementsList -> Int
sumDisplayWidths elmList = case (elmList) of
    ElementsListInner elem remList ->
                        addI (getDisplayWidth (getDisplayDataOfElement elem))
                             (sumDisplayWidths remList)
    ElementsListEnd elem  -> (getDisplayWidth (getDisplayDataOfElement elem))


getMaxDisplayWidth :: HorizContainerList -> Int
getMaxDisplayWidth hzList = case (hzList) of
    HorizContainerListInner hzContainer remList ->
        maxI (getDisplayWidth ( getDisplayDataOfHrzContainer hzContainer))
             (getMaxDisplayWidth remList)
    HorizContainerListEnd hzContainer ->
        (getDisplayWidth ( getDisplayDataOfHrzContainer hzContainer))


-- **computeHeight** a traversal that computes the height of each element
-- in the render tree this traversal depend on computing the width

computeHeightDoc :: Document -> Document
computeHeightDoc doc = case (doc) of
    Document pList  -> Document (computeHeightPList pList)

computeHeightPList :: PageList -> PageList
computeHeightPList pList = case (pList) of
    PageListInner page remList -> PageListInner (computeHeightPage page)
        (computeHeightPList remList)
    PageListEnd page -> PageListEnd (computeHeightPage page)

computeHeightPage :: Page -> Page
computeHeightPage p = case (p) of
    Page hzList displayData ->
        let hzList' = computeHeightHzList hzList
        in let newHeight = getSumHeights hzList'
           in Page hzList' (setDisplayHeight displayData newHeight )

computeHeightHzList :: HorizContainerList -> HorizContainerList
computeHeightHzList hzList = case (hzList) of
    HorizContainerListInner container remList ->
        let container' = computeHeightHzContainer container
            remList' = computeHeightHzList remList
        in HorizContainerListInner container'  remList'
    HorizContainerListEnd container ->
        HorizContainerListEnd (computeHeightHzContainer container)

computeHeightHzContainer :: HrzContainer -> HrzContainer
computeHeightHzContainer container =  case (container) of
        HrzContainer elmList displayData ->
            let elmList' = computeHeightElmList elmList in
            let maxHeight = getMaxHeight elmList' in
            let displayData' = setDisplayHeight displayData maxHeight in
            HrzContainer elmList' displayData'

computeHeightElmList :: ElementsList -> ElementsList
computeHeightElmList elmList = case (elmList) of
    ElementsListInner element remList ->
        ElementsListInner (computeHeightElement element)
           (computeHeightElmList remList)
    ElementsListEnd element -> ElementsListEnd (computeHeightElement  element)

computeHeightElement :: Element -> Element
computeHeightElement element = case (element) of
    VertContainer hzList displayData->
        let hzList'=   computeHeightHzList hzList in
        let newHeight = getSumHeights hzList' in
        VertContainer  hzList' (setDisplayHeight displayData newHeight)
    ImageCons imgWFixed ratio imgUrl displayData ->
        let w = getDisplayWidth displayData in
        let newH = ratio * w in --todo : not the correct computation
        ImageCons imgWFixed ratio imgUrl (setDisplayHeight displayData newH)
    TextBoxCons txtWFixed txtContent displayData ->
        let newH = (getStrLength txtContent) - (getDisplayWidth displayData) in
        -- TODO : should be division
        TextBoxCons txtWFixed txtContent (setDisplayHeight displayData newH)

getSumHeights :: HorizContainerList -> Int
getSumHeights hzList = case (hzList) of
    HorizContainerListInner container remList ->
        addI (getDisplayHeight (getDisplayDataOfHrzContainer container))
                (getSumHeights remList)
    HorizContainerListEnd container ->
        getDisplayHeight (getDisplayDataOfHrzContainer container)

getMaxHeight :: ElementsList -> Int
getMaxHeight elmList = case (elmList) of
    ElementsListInner element remList ->
        let h1 = getMaxHeight remList
            h2 = getDisplayHeight (getDisplayDataOfElement element)
        in maxI h1 h2
    ElementsListEnd element ->
        getDisplayHeight (getDisplayDataOfElement element)


-- --A pass that computer the initial x,y position for each element in the
-- -- document (within each page)
-- setPositionsDoc :: Document -> Document
-- setPositionsDoc doc = case (doc) of
--     Document pList  -> Document  (setPositionsPList pList)

-- setPositionsPList :: PageList -> PageList
-- setPositionsPList pList = case (pList) of
--     PageListInner page remList -> PageListInner (setPositionsPage page)
--       (setPositionsPList remList)
--     PageListEnd page -> PageListEnd (setPositionsPage page)

-- setPositionsPage :: Page -> Page
-- setPositionsPage page = case page of
--     Page hzList displayData ->
--         let   displayData' = setDisplayPosX (setDisplayPosY  displayData 0)  0
--         in Page (setPositionsHzList hzList 0 0) displayData'

-- setPositionsHzList :: HorizContainerList -> Int -> Int -> HorizContainerList
-- setPositionsHzList hzList curX  curY = case (hzList) of
--     HorizContainerListInner elmList remList ->
--         let  elmList' = setPositionsElmList elmList curX curY
--           in let elmListMaxHeight = getMaxHeight elmList
--              in let remList' = setPositionsHzList remList curX
--                      (addI curY elmListMaxHeight)
--                  in HorizContainerListInner elmList' remList'
--     HorizContainerListEnd elmList ->
--         HorizContainerListEnd ( setPositionsElmList elmList curX curY)

-- setPositionsElmList :: ElementsList -> Int -> Int -> ElementsList
-- setPositionsElmList elmList curX curY = case (elmList) of
--     ElementsListInner element remList ->
--         let element' = setPositionsElm element curX curY
--           in let elementWidth = getDisplayWidthElement element
--             in let remList' = setPositionsElmList remList (addI curX elementWidth) curY
--               in ElementsListInner element'    remList'
--     ElementsListEnd element ->
--         ElementsListEnd (setPositionsElm element curX curY)

-- setPositionsElm:: Element -> Int -> Int -> Element
-- setPositionsElm element curX curY = case (element) of
--     VertContainer hzList displayData->
--         let hzList'=   setPositionsHzList hzList  curX curY
--             in let displayData' =  setDisplayPosX (setDisplayPosY displayData curY )  curX
--               in   VertContainer  hzList' displayData'

--     ImageCons a b c displayData -> ImageCons a b c
--       (setDisplayPosX (setDisplayPosY displayData curY )   curX)
--     TextBoxCons a b c displayData -> TextBoxCons a b c
--       (setDisplayPosX (setDisplayPosY displayData curY )  curX)


buildElmList:: Int -> ElementsList
buildElmList n =
   if ( n==0 )
       then  ElementsListEnd (buildLeafElem 0)
       else  ElementsListInner (buildLeafElem n) (buildElmList (n-1))

buildLeafElem ::Int-> Element
buildLeafElem i =
 if(i == 0 )
   then TextBoxCons i StrEnd buildEmptyDisplayData
   else VertContainer (buildHorizContainerList (i-1)) buildEmptyDisplayData

buildDoc1 :: Document
buildDoc1 = Document (buildPageList1 1)

buildPageList1 :: Int -> PageList
buildPageList1 n =
 if (n == 0)
     then PageListEnd (buildPage1 1)
     else PageListInner (buildPage1 1) (buildPageList1 (n-1))

buildEmptyDisplayData :: DisplayData
buildEmptyDisplayData = DisplayDataK 1 1 1 1  (FontStyleK 1 1 1)


buildPage1 :: Int -> Page
buildPage1 n =
    Page (buildHorizContainerList n) buildEmptyDisplayData

buildHorizContainerList :: Int -> HorizContainerList
buildHorizContainerList n =
   if (n == 0)
      then  HorizContainerListEnd  (buildHrzContainer n )
      else HorizContainerListInner (buildHrzContainer n) (buildHorizContainerList (n-1))

buildHrzContainer:: Int -> HrzContainer
buildHrzContainer n =
   HrzContainer (buildElmList n) buildEmptyDisplayData

-- render :: Document -> Document
-- render doc =


gibbon_main = (computeHeightDoc( computeDisplayWidthDoc buildDoc1))
-- gibbon_main =  (computeHeightHzContainer( computeDisplayWidthHzContainer  (Document (buildHrzContainer 1))))
