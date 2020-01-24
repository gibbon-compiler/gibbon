module RenderTree where

data BOOL = TBool | FBool

-- We don't have a built-in Float right now.
data DisplayData = DisplayDataK  Int Int Int Int FontStyle
--DisplayDataK  posX posY height width fontStyle

data FontStyle = FontStyleK IntJ Int Int Int --strength
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
              | VertContainer Int Int HorizContainerList DisplayData --takes margin and borderWidth

data StringJ  = StrChar Int StringJ
              | StrEnd

data IntJ = ZeroJ |
            SucJ IntJ

notZero :: IntJ -> BOOL
notZero a = case a of
    ZeroJ ->  FBool
    SucJ  x -> TBool

--check if a is smaller than b
isSmaller :: IntJ -> IntJ -> BOOL
isSmaller a b =
  case a of
    ZeroJ -> notZero b
    SucJ a' -> isSmallerHelper a' b

isSmallerHelper :: IntJ -> IntJ -> BOOL
isSmallerHelper a' b =
 case b of
    ZeroJ -> FBool
    SucJ b' -> isSmaller a' b'

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

getMarginOfElement :: Element -> Int
getMarginOfElement elem = case (elem) of
    ImageCons imgWFixed ratio imgUrl displayData -> 0
    TextBoxCons  txtWFixed txtContent displayData -> 0
    VertContainer marginH bWidth hzList displayData -> marginH

getDisplayDataOfElement :: Element -> DisplayData
getDisplayDataOfElement element = case (element) of
    ImageCons imgWFixed ratio imgUrl displayData -> displayData
    TextBoxCons  txtWFixed txtContent displayData -> displayData
    VertContainer marginH bWidth hzList displayData -> displayData

getDisplayWidth :: DisplayData -> Int
getDisplayWidth displayData  = case (displayData) of
    DisplayDataK  posX posY height width fontStyle -> width

getDisplayHeight :: DisplayData -> Int
getDisplayHeight displayData  = case (displayData) of
    DisplayDataK  posX posY height width fontStyle -> height

setDisplayWidth :: DisplayData -> Int -> DisplayData
setDisplayWidth displayData newWidth = case (displayData) of
    DisplayDataK  posX posY height width fontStyle ->
        DisplayDataK  posX posY height newWidth fontStyle

getDisplayFontStyle :: DisplayData -> FontStyle
getDisplayFontStyle displayData = case (displayData) of
    DisplayDataK  posX posY height width fontStyle ->
         fontStyle

setDisplayFontStyle :: DisplayData -> FontStyle -> DisplayData
setDisplayFontStyle displayData f = case (displayData) of
    DisplayDataK  posX posY height width fontStyle ->
          DisplayDataK  posX posY height width f

setDisplayHeight :: DisplayData -> Int -> DisplayData
setDisplayHeight displayData newHeight = case (displayData) of
    DisplayDataK   posX posY height width fontStyle ->
        DisplayDataK  posX posY newHeight width fontStyle

setDisplayPosX :: DisplayData -> Int -> DisplayData
setDisplayPosX displayData x = case (displayData) of
    DisplayDataK  posX posY height width fontStyle ->
        DisplayDataK  x posY height width fontStyle

setDisplayPosY :: DisplayData -> Int -> DisplayData
setDisplayPosY displayData y = case (displayData) of
    DisplayDataK  posX posY height width fontStyle ->
        DisplayDataK  posX y height width fontStyle

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
    VertContainer marginH bWidth hzList  displayData->
        let hzList' = computeDisplayWidthHzLst hzList in
        let maxWidth = getMaxDisplayWidth hzList' in
        let maxWidth' = maxWidth + bWidth + bWidth in
        let displayData' = setDisplayWidth displayData  maxWidth'   in
        VertContainer marginH bWidth hzList' displayData'
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

getFontStyleStrength :: FontStyle -> IntJ
getFontStyleStrength font = case (font) of
  FontStyleK strength type_ size_ args_ -> strength



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
    VertContainer marginH bWidth hzList displayData->
        let hzList'=   computeHeightHzList hzList in
        let newHeight = getSumHeights hzList' in
        let newHeight' = newHeight + bWidth+ bWidth in
        VertContainer marginH bWidth  hzList' (setDisplayHeight displayData newHeight')
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

--A pass that computer the initial x, position for each element in the
-- document (within each page)
setPositionXDoc :: Document -> Document
setPositionXDoc doc = case (doc) of
    Document pList  -> Document  (setPositionXPList pList)

setPositionXPList :: PageList -> PageList
setPositionXPList pList = case (pList) of
    PageListInner page remList -> PageListInner (setPositionXPage page)
      (setPositionXPList remList)
    PageListEnd page -> PageListEnd (setPositionXPage page)

setPositionXPage :: Page -> Page
setPositionXPage page = case page of
    Page hzList displayData ->
        let   displayData' = setDisplayPosX  displayData  0
        in Page (setPositionXHzList hzList 0 ) displayData'

setPositionXHzList :: HorizContainerList -> Int -> HorizContainerList
setPositionXHzList hzList curX  = case (hzList) of
    HorizContainerListInner hzContainer remList ->
          let hzContainer' = setPositionXHrzContainer hzContainer curX
             in let remList' = setPositionXHzList remList curX
                 in HorizContainerListInner hzContainer' remList'
    HorizContainerListEnd hzContainer ->
        HorizContainerListEnd ( setPositionXHrzContainer hzContainer curX )

setPositionXHrzContainer:: HrzContainer -> Int -> HrzContainer
setPositionXHrzContainer container curX = case (container) of
    HrzContainer elmList displayData ->
      let elmList' = setPositionXElmList  elmList curX in
      let displayData' = setDisplayPosX displayData curX in
      HrzContainer elmList'  displayData'

setPositionXElmList :: ElementsList  -> Int -> ElementsList
setPositionXElmList elmList curX  = case (elmList) of
    ElementsListInner element remList ->
        let element' = setPositionXElm element curX  in
        let elementWidth = getDisplayWidth (getDisplayDataOfElement element) in
        let margin = getMarginOfElement element in
        let remList' = setPositionXElmList remList (curX + margin)
        in ElementsListInner element' remList'
    ElementsListEnd element ->
        ElementsListEnd (setPositionXElm element curX )

setPositionXElm:: Element -> Int  -> Element
setPositionXElm element curX   = case (element) of
    VertContainer marginH bWidth hzList displayData->
        let margin = getMarginOfElement  element in
        let hzList'=   setPositionXHzList hzList  (curX+margin) in
        let displayData' =  setDisplayPosX displayData (curX +margin)  in
        VertContainer marginH bWidth hzList' displayData'
    ImageCons imgWFixed ratio imgUrl displayData ->
        let margin = getMarginOfElement  element in
       ImageCons imgWFixed ratio imgUrl (setDisplayPosX displayData (curX+margin))
    TextBoxCons txtWFixed txtContent displayData ->
       let margin = getMarginOfElement  element in
       TextBoxCons txtWFixed txtContent (setDisplayPosX displayData (curX+margin))


--A pass that computer the initial y, position for each element in the
-- document (within each page)
setPositionYDoc :: Document -> Document
setPositionYDoc doc = case (doc) of
    Document pList  -> Document  (setPositionYPList pList)

setPositionYPList :: PageList -> PageList
setPositionYPList pList = case (pList) of
    PageListInner page remList -> PageListInner (setPositionYPage page)
      (setPositionYPList remList)
    PageListEnd page -> PageListEnd (setPositionYPage page)

setPositionYPage :: Page -> Page
setPositionYPage page = case page of
    Page hzList displayData ->
        let   displayData' = setDisplayPosY  displayData  0
        in Page (setPositionXHzList hzList 0 ) displayData'

setPositionYHzList :: HorizContainerList -> Int -> HorizContainerList
setPositionYHzList hzList curY  = case (hzList) of
    HorizContainerListInner hzContainer remList ->
        let hzContainer' = setPositionYHrzContainer hzContainer curY in
        let containerHeight = getDisplayHeight (getDisplayDataOfHrzContainer hzContainer) in
        let remList' = setPositionYHzList remList (curY + containerHeight)
        in  HorizContainerListInner hzContainer' remList'
    HorizContainerListEnd hzContainer ->
        HorizContainerListEnd ( setPositionYHrzContainer hzContainer curY )

setPositionYHrzContainer:: HrzContainer -> Int -> HrzContainer
setPositionYHrzContainer container curY = case (container) of
    HrzContainer elmList displayData ->
      let elmList' = setPositionYElmList  elmList curY in
      let displayData' = setDisplayPosY displayData curY in
      HrzContainer elmList'  displayData'

setPositionYElmList :: ElementsList -> Int -> ElementsList
setPositionYElmList elmList curY  = case (elmList) of
    ElementsListInner element remList ->
        let element' = setPositionYElm element curY
            in let remList' = setPositionYElmList remList curY
              in ElementsListInner element' remList'
    ElementsListEnd element ->
        ElementsListEnd (setPositionYElm element curY )

setPositionYElm:: Element -> Int -> Element
setPositionYElm element curY  = case (element) of
    VertContainer marginH bWidth hzList displayData->
        let hzList'=   setPositionYHzList hzList  curY in
        let displayData' =  setDisplayPosY displayData curY  in
        VertContainer marginH bWidth  hzList' displayData'
    ImageCons imgWFixed ratio imgUrl displayData ->
       ImageCons imgWFixed ratio imgUrl (setDisplayPosY displayData curY)
    TextBoxCons txtWFixed txtContent displayData ->
       TextBoxCons txtWFixed txtContent (setDisplayPosY displayData curY)


-- A pass that propagate font info down from the containers to the elements that
-- do not lie with in other containers
propagateContainerFontDoc :: Document -> FontStyle -> Document
propagateContainerFontDoc doc fStyleDefault = case (doc) of
    Document pList  -> Document  (propagateContainerFontPList pList fStyleDefault)

propagateContainerFontPList :: PageList -> FontStyle  -> PageList
propagateContainerFontPList pList fStyleDefault = case (pList) of
    PageListInner page remList -> PageListInner (propagateContainerFontPage page fStyleDefault)
      (propagateContainerFontPList remList fStyleDefault)
    PageListEnd page -> PageListEnd (propagateContainerFontPage page fStyleDefault)

propagateContainerFontPage :: Page -> FontStyle   -> Page
propagateContainerFontPage page fStyleDefault= case page of
    Page hzList displayData ->
         Page (propagateContainerFontHzList hzList fStyleDefault) displayData


propagateContainerFontHzList :: HorizContainerList -> FontStyle -> HorizContainerList
propagateContainerFontHzList hzList strongestFont  = case (hzList) of
    HorizContainerListInner hzContainer remList ->
        let hzContainer' = propagateContainerFontHrzContainer hzContainer strongestFont in
        let remList' = propagateContainerFontHzList remList strongestFont
        in  HorizContainerListInner hzContainer' remList'
    HorizContainerListEnd hzContainer ->
        HorizContainerListEnd ( propagateContainerFontHrzContainer hzContainer strongestFont )



retFirstIfTrue :: BOOL -> FontStyle -> FontStyle -> FontStyle
retFirstIfTrue b f1 f2 = case b of
    TBool -> f1
    FBool -> f2

-- reach here
propagateContainerFontHrzContainer:: HrzContainer -> FontStyle -> HrzContainer
propagateContainerFontHrzContainer container strongestFont   = case (container) of
    HrzContainer elmList displayData ->
        let strengthMax  = getFontStyleStrength strongestFont in
        let strengthCur =  getFontStyleStrength (getDisplayFontStyle displayData) in
        let flag =  isSmaller  strengthCur  strengthMax  in
        let strongestFont' = retFirstIfTrue  flag strongestFont (getDisplayFontStyle displayData)  in
        let elmList' = propagateContainerFontElmList elmList  strongestFont' in
      HrzContainer  elmList' (setDisplayFontStyle displayData strongestFont')

propagateContainerFontElmList :: ElementsList -> FontStyle -> ElementsList
propagateContainerFontElmList  elmList strongestFont  = case (elmList) of
    ElementsListInner element remList ->
        let element' = propagateContainerFontElm element strongestFont
            in let remList' = propagateContainerFontElmList remList strongestFont
              in ElementsListInner element' remList'
    ElementsListEnd element ->
        ElementsListEnd (propagateContainerFontElm element strongestFont )

propagateContainerFontElm:: Element -> FontStyle -> Element
propagateContainerFontElm element strongestFont  = case (element) of
    VertContainer marginH bWidth hzList displayData->
      let strengthMax  = getFontStyleStrength strongestFont in
      let strengthCur =  getFontStyleStrength (getDisplayFontStyle displayData) in
      let flag =  isSmaller    strengthCur strengthMax  in
      let strongestFont' = retFirstIfTrue  flag strongestFont (getDisplayFontStyle displayData)  in
      let  hzList' = propagateContainerFontHzList hzList strongestFont' in
      VertContainer marginH bWidth  hzList' (setDisplayFontStyle displayData strongestFont')

    ImageCons imgWFixed ratio imgUrl displayData ->
      let strengthMax  = getFontStyleStrength strongestFont in
      let strengthCur =  getFontStyleStrength (getDisplayFontStyle displayData) in
      let flag =  isSmaller    strengthCur strengthMax  in
      let strongestFont' = retFirstIfTrue  flag strongestFont (getDisplayFontStyle displayData)  in
      ImageCons imgWFixed ratio imgUrl (setDisplayFontStyle displayData strongestFont')


    TextBoxCons txtWFixed txtContent displayData ->
      let strengthMax  = getFontStyleStrength strongestFont in
      let strengthCur =  getFontStyleStrength (getDisplayFontStyle displayData) in
      let flag =  isSmaller    strengthCur strengthMax  in
      let strongestFont' = retFirstIfTrue  flag strongestFont (getDisplayFontStyle displayData)  in
      TextBoxCons txtWFixed txtContent (setDisplayFontStyle displayData strongestFont')

buildElmList:: Int -> ElementsList
buildElmList n =
   if ( n==0 )
       then  ElementsListEnd (buildLeafElem 0)
       else  ElementsListInner (buildLeafElem n) (buildElmList (n-1))

buildStr:: Int -> StringJ
buildStr size =
 if size ==0
   then StrEnd
   else (StrChar 10) (buildStr (size -1))

buildLeafElem ::Int-> Element
buildLeafElem i =
 if(i == 0 )
   then TextBoxCons i  (buildStr 100)  buildEmptyDisplayData
   else VertContainer 1 2 (buildHorizContainerList (i-1)) buildEmptyDisplayData

buildDoc1 :: Document
buildDoc1 = Document (buildPageList1 1)

buildPageList1 :: Int -> PageList
buildPageList1 n =
 if (n == 0)
     then PageListEnd (buildPage1 1)
     else PageListInner (buildPage1 1) (buildPageList1 (n-1))

buildEmptyDisplayData :: DisplayData
buildEmptyDisplayData = DisplayDataK  1 1 1 1  (FontStyleK  (ZeroJ) 1 1 1)


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
-- gibbon_main =  propagateContainerFontDoc (computeHeightDoc( computeDisplayWidthDoc buildDoc1))

-- gibbon_main =   (computeHeightDoc( computeDisplayWidthDoc buildDoc1))

gibbon_main =  (setPositionXDoc (computeHeightDoc( computeDisplayWidthDoc buildDoc1)))


-- gibbon_main = (setPositionYDoc (setPositionXDoc (computeHeightDoc(
--                  propagateContainerFontDoc( computeDisplayWidthDoc buildDoc1) (FontStyleK (SucJ ZeroJ) 1 1 1) ))))

-- -- gibbon_main =  (computeHeightHzContainer( computeDisplayWidthHzContainer  (Document (buildHrzContainer 1))))
