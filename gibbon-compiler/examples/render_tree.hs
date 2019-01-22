data NodeData = NodeData Int Int Int Int Float MeasureMode FontStyle 
 getMesureMode :: NodeData -> MeasureMode
 
data MeasureMode = Flex | Relative | Absolute 
data FontStyle = FontStyle Int Int Int 

-- class Data {
--     public:
--       int PosX = 0;
--       int PosY = 0;
--       int Height = 0;
--       int Width = 0;
--       float RelWidth;
--       MEASURE_MODE WMode;
--       FontInfo FontStyle;
-- };
-- struct FontInfo {
--     public:
--       unsigned int Type = -1;
--       unsigned int Size = -1;
--       unsigned int Color = -1;
--     };

data Document = Document PageList NodeData
data PageList = PageListInner Page PageList  NodeData
              | PageListEnd Page NodeData
data Page     = Page HorizContainerList NodeData
data HorizContainerList = HorizContainerListInner ElementsList HorizContainerList NodeData
                        | HorizContainerListEnd ElementsList NodeData

data ElementsList       = ElementsListInner  Element ElementsList NodeData
                        | ElementsListEnd Element NodeData
data Element =  ImageCons Int Int StringJ NodeData
              | TextBoxCons Int Int StringJ NodeData
              | VertContainer HorizContainerList NodeData
data StringJ  = StrChar Char 
             | StrEnd

resolveFlexWidthDoc :: Document -> Document 
resolveFlexWidthDoc doc = case (doc) of
     Document pgList -> Document (resolveFlexWidthPList pgList)

resolveFlexWidthPList :: PageList -> PageList 
resolveFlexWidthPList pgList = case (pgList) of
    PageListInner page remList ->
        PageListInner (resolveFlexWidthP page) (resolveFlexWidthPList remList)
    PageListEnd page -> 
        PageListEnd (resolveFlexWidthP page)

resolveFlexWidthP :: Page -> Page
resolveFlexWidthP p  = case (p) of 
    Page hzList -> If Page (resolveFlexWidthHzLst hzList)

resolveFlexWidthHzLst :: HorizContainerList -> HorizContainerList
resolveFlexWidthHzLst hzList  = case (hzList) of 
    HorizContainerListInner  elmList remList ->
        HorizContainerListInner (resolveFlexWidthElmList elmList) 
           (resolveFlexWidthHzLst remList)
    HorizContainerListEnd elmList -> 
        HorizContainerListEnd (resolveFlexWidthElmList elmList)

resolveFlexWidthElmList ::ElementsList -> ElementsList
resolveFlexWidthElmList elemList  = case (elemList) of 
    ElementsListInner element remList ->
        ElementsListInner (resolveFlexWidthElm element) 
            (resolveFlexWidthElmList remList)
    ElementsListEnd element -> 
        ElementsListEnd (resolveFlexWidthElm element)

resolveFlexWidthElm ::Element -> Element
resolveFlexWidthElm element  = case (element) of 
    VertContainer hzList  -> VertContainer (resolveFlexWidthHzLst hzList)

main =  StrEnd


