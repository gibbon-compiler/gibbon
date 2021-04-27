{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}

module Main where

-- Gibbon Prelude --

import Prelude as P ( (==), id, print, lookup, ($)
                    , Int, (+), (-), (*), quot, (<), (>), (<=), (>=), (^), mod
                    , Bool(..), (||), (&&)
                    , String, (++)
                    , Show, Eq, IO)

import Data.Maybe (fromJust, isJust)


gibbon_bench :: String -> (a -> b) -> a -> b
gibbon_bench _str fn arg = fn arg

type Sym = String

type Dict a = [(Sym,a)]

timeit :: a -> a
timeit = id

rand :: Int
rand = 10

(/) :: Int -> Int -> Int
(/) = quot

eqsym :: Sym -> Sym -> Bool
eqsym = (==)

mod :: Int -> Int -> Int
mod = P.mod


sizeParam :: Int
sizeParam = 4

dictEmpty _a = []

dictInsert _a d x v = (x,v):d

dictLookup d k = fromJust $ lookup k d

dictHaskey d k = isJust $ lookup k d

-- Gibbon Prelude ends --

data NodeData = NodeDataK Int Int Int Int Int FontStyle 
  deriving Show
data FontStyle = FontStyleK Int Int Int 
  deriving Show
data Document = Document PageList 
  deriving Show
data PageList = PageListInner Page PageList | 
                PageListEnd Page 
  deriving Show
data Page = Page HorizContainerList NodeData 
  deriving Show
data HorizContainerList = HorizContainerListInner ElementsList HorizContainerList | 
                          HorizContainerListEnd ElementsList 
  deriving Show
data ElementsList = ElementsListInner Element ElementsList | 
                    ElementsListEnd Element 
  deriving Show
data Element = ImageCons Int Int StringJ NodeData | 
               TextBoxCons Int Int StringJ NodeData | 
               VertContainer HorizContainerList NodeData 
  deriving Show
data StringJ = StrChar Int | 
               StrEnd 
  deriving Show
maxI :: Int -> Int -> Int
maxI a_244_770_1025 b_245_771_1026 =
    let fltIf_978_1027 :: Bool = a_244_770_1025 > b_245_771_1026 in
    if fltIf_978_1027
    then a_244_770_1025
    else b_245_771_1026

setPositionsElm :: Element -> Int -> Int -> Element
setPositionsElm element_246_772_1028 curX_247_773_1029 curY_248_774_1030 =
    case element_246_772_1028 of
        VertContainer hzList_249_775_1031 nData_250_776_1032 ->
            let hzList__251_777_1033 :: HorizContainerList = setPositionsHzList hzList_249_775_1031 curX_247_773_1029 curY_248_774_1030 in
            let fltAppE_979_1034 :: NodeData = updatePosY nData_250_776_1032 curY_248_774_1030 in
            let nData__252_778_1035 :: NodeData = updatePosX fltAppE_979_1034 curX_247_773_1029 in
            (VertContainer hzList__251_777_1033 nData__252_778_1035)
        ImageCons a_253_779_1036 b_254_780_1037 c_255_781_1038 nData_256_782_1039 ->
            let fltAppE_981_1040 :: NodeData = updatePosY nData_256_782_1039 curY_248_774_1030 in
            let fltPkd_980_1041 :: NodeData = updatePosX fltAppE_981_1040 curX_247_773_1029 in
            (ImageCons a_253_779_1036 b_254_780_1037 c_255_781_1038 fltPkd_980_1041)
        TextBoxCons a_257_783_1042 b_258_784_1043 c_259_785_1044 nData_260_786_1045 ->
            let fltAppE_983_1046 :: NodeData = updatePosY nData_260_786_1045 curY_248_774_1030 in
            let fltPkd_982_1047 :: NodeData = updatePosX fltAppE_983_1046 curX_247_773_1029 in
            (TextBoxCons a_257_783_1042 b_258_784_1043 c_259_785_1044 fltPkd_982_1047)

setPositionsElmList :: ElementsList -> Int -> Int -> ElementsList
setPositionsElmList elmList_261_787_1048 curX_262_788_1049 curY_263_789_1050 =
    case elmList_261_787_1048 of
        ElementsListInner element_264_790_1051 remList_265_791_1052 ->
            let element__266_792_1053 :: Element = setPositionsElm element_264_790_1051 curX_262_788_1049 curY_263_789_1050 in
            let elementWidth_267_793_1054 :: Int = getWidthElement element_264_790_1051 in
            let fltAppE_984_1055 :: Int = addI curX_262_788_1049 elementWidth_267_793_1054 in
            let remList__268_794_1056 :: ElementsList = setPositionsElmList remList_265_791_1052 fltAppE_984_1055 curY_263_789_1050 in
            (ElementsListInner element__266_792_1053 remList__268_794_1056)
        ElementsListEnd element_269_795_1057 ->
            let fltPkd_985_1058 :: Element = setPositionsElm element_269_795_1057 curX_262_788_1049 curY_263_789_1050 in
            (ElementsListEnd fltPkd_985_1058)

setPositionsHzList :: HorizContainerList -> Int -> Int -> HorizContainerList
setPositionsHzList hzList_270_796_1059 curX_271_797_1060 curY_272_798_1061 =
    case hzList_270_796_1059 of
        HorizContainerListInner elmList_273_799_1062 remList_274_800_1063 ->
            let elmList__275_801_1064 :: ElementsList = setPositionsElmList elmList_273_799_1062 curX_271_797_1060 curY_272_798_1061 in
            let elmListMaxHeight_276_802_1065 :: Int = getMaxHeight elmList_273_799_1062 in
            let fltAppE_986_1066 :: Int = addI curY_272_798_1061 elmListMaxHeight_276_802_1065 in
            let remList__277_803_1067 :: HorizContainerList = setPositionsHzList remList_274_800_1063 curX_271_797_1060 fltAppE_986_1066 in
            (HorizContainerListInner elmList__275_801_1064 remList__277_803_1067)
        HorizContainerListEnd elmList_278_804_1068 ->
            let fltPkd_987_1069 :: ElementsList = setPositionsElmList elmList_278_804_1068 curX_271_797_1060 curY_272_798_1061 in
            (HorizContainerListEnd fltPkd_987_1069)

setPositionsPage :: Page -> Page
setPositionsPage page_279_805_1070 =
    case page_279_805_1070 of
        Page hzList_280_806_1071 nData_281_807_1072 ->
            let fltAppE_988_1073 :: NodeData = updatePosY nData_281_807_1072 0 in
            let nData__282_808_1074 :: NodeData = updatePosX fltAppE_988_1073 0 in
            let fltPkd_989_1075 :: HorizContainerList = setPositionsHzList hzList_280_806_1071 0 0 in
            (Page fltPkd_989_1075 nData__282_808_1074)

setPositionsPList :: PageList -> PageList
setPositionsPList pList_283_809_1076 =
    case pList_283_809_1076 of
        PageListInner page_284_810_1077 remList_285_811_1078 ->
            let fltPkd_990_1079 :: Page = setPositionsPage page_284_810_1077 in
            let fltPkd_991_1080 :: PageList = setPositionsPList remList_285_811_1078 in
            (PageListInner fltPkd_990_1079 fltPkd_991_1080)
        PageListEnd page_286_812_1081 ->
            let fltPkd_992_1082 :: Page = setPositionsPage page_286_812_1081 in
            (PageListEnd fltPkd_992_1082)

setPositionsDoc :: Document -> Document
setPositionsDoc doc_287_813_1083 =
    case doc_287_813_1083 of
        Document pList_288_814_1084 ->
            let fltPkd_993_1085 :: PageList = setPositionsPList pList_288_814_1084 in
            (Document fltPkd_993_1085)

computeHeightElement :: Element -> Element
computeHeightElement element_289_815_1086 =
    case element_289_815_1086 of
        VertContainer hzList_290_816_1087 nData_291_817_1088 ->
            let hzList__292_818_1089 :: HorizContainerList = computeHeightHzList hzList_290_816_1087 in
            let newHeight_293_819_1090 :: Int = getSumHeights hzList__292_818_1089 in
            let fltPkd_994_1091 :: NodeData = updateHeight nData_291_817_1088 newHeight_293_819_1090 in
            (VertContainer hzList__292_818_1089 fltPkd_994_1091)
        ImageCons a_294_820_1092 b_295_821_1093 c_296_822_1094 d_297_823_1095 ->
            (ImageCons a_294_820_1092 b_295_821_1093 c_296_822_1094 d_297_823_1095)
        TextBoxCons a_298_824_1096 b_299_825_1097 c_300_826_1098 d_301_827_1099 ->
            (TextBoxCons a_298_824_1096 b_299_825_1097 c_300_826_1098 d_301_827_1099)

computeHeightElmList :: ElementsList -> ElementsList
computeHeightElmList elmList_302_828_1100 =
    case elmList_302_828_1100 of
        ElementsListInner element_303_829_1101 remList_304_830_1102 ->
            let fltPkd_995_1103 :: Element = computeHeightElement element_303_829_1101 in
            let fltPkd_996_1104 :: ElementsList = computeHeightElmList remList_304_830_1102 in
            (ElementsListInner fltPkd_995_1103 fltPkd_996_1104)
        ElementsListEnd element_305_831_1105 ->
            let fltPkd_997_1106 :: Element = computeHeightElement element_305_831_1105 in
            (ElementsListEnd fltPkd_997_1106)

computeHeightHzList :: HorizContainerList -> HorizContainerList
computeHeightHzList hzList_306_832_1107 =
    case hzList_306_832_1107 of
        HorizContainerListInner elmList_307_833_1108 remList_308_834_1109 ->
            let elmList__309_835_1110 :: ElementsList = computeHeightElmList elmList_307_833_1108 in
            let remList__310_836_1111 :: HorizContainerList = computeHeightHzList remList_308_834_1109 in
            (HorizContainerListInner elmList__309_835_1110 remList__310_836_1111)
        HorizContainerListEnd elmList_311_837_1112 ->
            let fltPkd_998_1113 :: ElementsList = computeHeightElmList elmList_311_837_1112 in
            (HorizContainerListEnd fltPkd_998_1113)

computeHeightPage :: Page -> Page
computeHeightPage p_312_838_1114 =
    case p_312_838_1114 of
        Page hzList_313_839_1115 nData_314_840_1116 ->
            let hzList__315_841_1117 :: HorizContainerList = computeHeightHzList hzList_313_839_1115 in
            let newHeight_316_842_1118 :: Int = getSumHeights hzList__315_841_1117 in
            let fltPkd_999_1119 :: NodeData = updateHeight nData_314_840_1116 newHeight_316_842_1118 in
            (Page hzList__315_841_1117 fltPkd_999_1119)

getMaxHeight :: ElementsList -> Int
getMaxHeight elmList_317_843_1120 =
    case elmList_317_843_1120 of
        ElementsListInner element_318_844_1121 remList_319_845_1122 ->
            let h1_320_846_1123 :: Int = getMaxHeight remList_319_845_1122 in
            let h2_321_847_1124 :: Int = getHeightElement element_318_844_1121 in
            maxI h1_320_846_1123 h2_321_847_1124
        ElementsListEnd element_322_848_1125 ->
            getHeightElement element_322_848_1125

getSumHeights :: HorizContainerList -> Int
getSumHeights hzList_323_849_1126 =
    case hzList_323_849_1126 of
        HorizContainerListInner elmList_324_850_1127 remList_325_851_1128 ->
            let maxH_326_852_1129 :: Int = getMaxHeight elmList_324_850_1127 in
            let fltAppE_1000_1130 :: Int = getSumHeights remList_325_851_1128 in
            addI maxH_326_852_1129 fltAppE_1000_1130
        HorizContainerListEnd elmList_327_853_1131 ->
            getMaxHeight elmList_327_853_1131

computeHeightPList :: PageList -> PageList
computeHeightPList pList_328_854_1132 =
    case pList_328_854_1132 of
        PageListInner page_329_855_1133 remList_330_856_1134 ->
            let fltPkd_1001_1135 :: Page = computeHeightPage page_329_855_1133 in
            let fltPkd_1002_1136 :: PageList = computeHeightPList remList_330_856_1134 in
            (PageListInner fltPkd_1001_1135 fltPkd_1002_1136)
        PageListEnd page_331_857_1137 ->
            let fltPkd_1003_1138 :: Page = computeHeightPage page_331_857_1137 in
            (PageListEnd fltPkd_1003_1138)

computeHeightDoc :: Document -> Document
computeHeightDoc doc_332_858_1139 =
    case doc_332_858_1139 of
        Document pList_333_859_1140 ->
            let fltPkd_1004_1141 :: PageList = computeHeightPList pList_333_859_1140 in
            (Document fltPkd_1004_1141)

resolveWidthElm :: Element -> Element
resolveWidthElm element_334_860_1142 =
    case element_334_860_1142 of
        VertContainer hzList_335_861_1143 nData_336_862_1144 ->
            let hzList__337_863_1145 :: HorizContainerList = resolveWidthHzLst hzList_335_861_1143 in
            let maxWidth_338_864_1146 :: Int = getMaxWidthHzList hzList__337_863_1145 in
            let nData__339_865_1147 :: NodeData = updateWidth nData_336_862_1144 maxWidth_338_864_1146 in
            (VertContainer hzList__337_863_1145 nData__339_865_1147)
        ImageCons a_340_866_1148 b_341_867_1149 c_342_868_1150 d_343_869_1151 ->
            (ImageCons a_340_866_1148 b_341_867_1149 c_342_868_1150 d_343_869_1151)
        TextBoxCons a_344_870_1152 b_345_871_1153 c_346_872_1154 d_347_873_1155 ->
            (TextBoxCons a_344_870_1152 b_345_871_1153 c_346_872_1154 d_347_873_1155)

resolveWidthElmList :: ElementsList -> ElementsList
resolveWidthElmList elemList_348_874_1156 =
    case elemList_348_874_1156 of
        ElementsListInner element_349_875_1157 remList_350_876_1158 ->
            let fltPkd_1005_1159 :: Element = resolveWidthElm element_349_875_1157 in
            let fltPkd_1006_1160 :: ElementsList = resolveWidthElmList remList_350_876_1158 in
            (ElementsListInner fltPkd_1005_1159 fltPkd_1006_1160)
        ElementsListEnd element_351_877_1161 ->
            let fltPkd_1007_1162 :: Element = resolveWidthElm element_351_877_1161 in
            (ElementsListEnd fltPkd_1007_1162)

resolveWidthHzLst :: HorizContainerList -> HorizContainerList
resolveWidthHzLst hzList_352_878_1163 =
    case hzList_352_878_1163 of
        HorizContainerListInner elmList_353_879_1164 remList_354_880_1165 ->
            let fltPkd_1008_1166 :: ElementsList = resolveWidthElmList elmList_353_879_1164 in
            let fltPkd_1009_1167 :: HorizContainerList = resolveWidthHzLst remList_354_880_1165 in
            (HorizContainerListInner fltPkd_1008_1166 fltPkd_1009_1167)
        HorizContainerListEnd elmList_355_881_1168 ->
            let fltPkd_1010_1169 :: ElementsList = resolveWidthElmList elmList_355_881_1168 in
            (HorizContainerListEnd fltPkd_1010_1169)

resolveWidthP :: Page -> Page
resolveWidthP p_356_882_1170 =
    case p_356_882_1170 of
        Page hzList_357_883_1171 nData_358_884_1172 ->
            let hzList__359_885_1173 :: HorizContainerList = resolveWidthHzLst hzList_357_883_1171 in
            let maxWidth_360_886_1174 :: Int = getMaxWidthHzList hzList__359_885_1173 in
            let nData__361_887_1175 :: NodeData = updateWidth nData_358_884_1172 maxWidth_360_886_1174 in
            (Page hzList__359_885_1173 nData__361_887_1175)

resolveWidthPList :: PageList -> PageList
resolveWidthPList pgList_362_888_1176 =
    case pgList_362_888_1176 of
        PageListInner page_363_889_1177 remList_364_890_1178 ->
            let fltPkd_1011_1179 :: Page = resolveWidthP page_363_889_1177 in
            let fltPkd_1012_1180 :: PageList = resolveWidthPList remList_364_890_1178 in
            (PageListInner fltPkd_1011_1179 fltPkd_1012_1180)
        PageListEnd page_365_891_1181 ->
            let fltPkd_1013_1182 :: Page = resolveWidthP page_365_891_1181 in
            (PageListEnd fltPkd_1013_1182)

resolveWidthDoc :: Document -> Document
resolveWidthDoc doc_366_892_1183 =
    case doc_366_892_1183 of
        Document pgList_367_893_1184 ->
            let fltPkd_1014_1185 :: PageList = resolveWidthPList pgList_367_893_1184 in
            (Document fltPkd_1014_1185)

sumWidthsElmList :: ElementsList -> Int
sumWidthsElmList elmList_368_894_1186 =
    case elmList_368_894_1186 of
        ElementsListInner e_369_895_1187 remList_370_896_1188 ->
            let fltAppE_1015_1189 :: Int = getWidthElement e_369_895_1187 in
            let fltAppE_1016_1190 :: Int = sumWidthsElmList remList_370_896_1188 in
            addI fltAppE_1015_1189 fltAppE_1016_1190
        ElementsListEnd e_371_897_1191 ->
            getWidthElement e_371_897_1191

getMaxWidthHzList :: HorizContainerList -> Int
getMaxWidthHzList hzList_372_898_1192 =
    case hzList_372_898_1192 of
        HorizContainerListInner elmList_373_899_1193 remList_374_900_1194 ->
            let fltAppE_1017_1195 :: Int = sumWidthsElmList elmList_373_899_1193 in
            let fltAppE_1018_1196 :: Int = getMaxWidthHzList remList_374_900_1194 in
            maxI fltAppE_1017_1195 fltAppE_1018_1196
        HorizContainerListEnd elmList_375_901_1197 ->
            sumWidthsElmList elmList_375_901_1197

updatePosY :: NodeData -> Int -> NodeData
updatePosY nData_376_902_1198 y_377_903_1199 =
    case nData_376_902_1198 of
        NodeDataK posX_378_904_1200 posY_379_905_1201 height_380_906_1202 width_381_907_1203 relWidth_382_908_1204 fontStyle_383_909_1205 ->
            (NodeDataK posX_378_904_1200 y_377_903_1199 height_380_906_1202 width_381_907_1203 relWidth_382_908_1204 fontStyle_383_909_1205)

updatePosX :: NodeData -> Int -> NodeData
updatePosX nData_384_910_1206 x_385_911_1207 =
    case nData_384_910_1206 of
        NodeDataK posX_386_912_1208 posY_387_913_1209 height_388_914_1210 width_389_915_1211 relWidth_390_916_1212 fontStyle_391_917_1213 ->
            (NodeDataK x_385_911_1207 posY_387_913_1209 height_388_914_1210 width_389_915_1211 relWidth_390_916_1212 fontStyle_391_917_1213)

updateHeight :: NodeData -> Int -> NodeData
updateHeight nData_392_918_1214 newHeight_393_919_1215 =
    case nData_392_918_1214 of
        NodeDataK posX_394_920_1216 posY_395_921_1217 height_396_922_1218 width_397_923_1219 relWidth_398_924_1220 fontStyle_399_925_1221 ->
            (NodeDataK posX_394_920_1216 posY_395_921_1217 newHeight_393_919_1215 width_397_923_1219 relWidth_398_924_1220 fontStyle_399_925_1221)

updateWidth :: NodeData -> Int -> NodeData
updateWidth nData_400_926_1222 newWidth_401_927_1223 =
    case nData_400_926_1222 of
        NodeDataK posX_402_928_1224 posY_403_929_1225 height_404_930_1226 width_405_931_1227 relWidth_406_932_1228 fontStyle_407_933_1229 ->
            (NodeDataK posX_402_928_1224 posY_403_929_1225 height_404_930_1226 newWidth_401_927_1223 relWidth_406_932_1228 fontStyle_407_933_1229)

getHeightElement :: Element -> Int
getHeightElement e_408_934_1230 =
    case e_408_934_1230 of
        ImageCons a_409_935_1231 b_410_936_1232 s_411_937_1233 nData_412_938_1234 ->
            getHeight nData_412_938_1234
        TextBoxCons a_413_939_1235 b_414_940_1236 s_415_941_1237 nData_416_942_1238 ->
            getHeight nData_416_942_1238
        VertContainer hzList_417_943_1239 x_418_944_1240 ->
            getSumHeights hzList_417_943_1239

getWidthElement :: Element -> Int
getWidthElement e_419_945_1241 =
    case e_419_945_1241 of
        ImageCons a_420_946_1242 b_421_947_1243 s_422_948_1244 nData_423_949_1245 ->
            getWidth nData_423_949_1245
        TextBoxCons a_424_950_1246 b_425_951_1247 s_426_952_1248 nData_427_953_1249 ->
            getWidth nData_427_953_1249
        VertContainer hzList_428_954_1250 x_429_955_1251 ->
            getMaxWidthHzList hzList_428_954_1250

getHeight :: NodeData -> Int
getHeight nData_430_956_1252 =
    case nData_430_956_1252 of
        NodeDataK posX_431_957_1253 posY_432_958_1254 height_433_959_1255 width_434_960_1256 relWidth_435_961_1257 fontStyle_436_962_1258 ->
            height_433_959_1255

getWidth :: NodeData -> Int
getWidth nData_437_963_1259 =
    case nData_437_963_1259 of
        NodeDataK posX_438_964_1260 posY_439_965_1261 height_440_966_1262 width_441_967_1263 relWidth_442_968_1264 fontStyle_443_969_1265 ->
            width_441_967_1263

addI :: Int -> Int -> Int
addI a_444_970_1266 b_445_971_1267 =
    a_444_970_1266 + b_445_971_1267

_FUS_f_computeHeightElement_f_resolveWidthElm_FUS_ :: Element -> Element
_FUS_f_computeHeightElement_f_resolveWidthElm_FUS_ inputTree_1296_1319 =
    case inputTree_1296_1319 of
        VertContainer hzList_335_861_1143_1268_1300_1320 nData_336_862_1144_1269_1301_1321 ->
            let tupled_output_2516 :: (Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP_ hzList_335_861_1143_1268_1300_1320
                (tupled_output_2516_proj_0,tupled_output_2516_proj_1,tupled_output_2516_proj_2) :: (Int,HorizContainerList,Int) = tupled_output_2516 in
            let fltPkd_994_1091_1286_1308_1327 :: NodeData = _FUS_f_updateHeight_f_updateWidth_FUS_ nData_336_862_1144_1269_1301_1321 tupled_output_2516_proj_2 tupled_output_2516_proj_0 in
            (VertContainer tupled_output_2516_proj_1 fltPkd_994_1091_1286_1308_1327)
        ImageCons a_340_866_1148_1273_1309_1328 b_341_867_1149_1274_1310_1329 c_342_868_1150_1275_1311_1330 d_343_869_1151_1276_1312_1331 ->
            (ImageCons a_340_866_1148_1273_1309_1328 b_341_867_1149_1274_1310_1329 c_342_868_1150_1275_1311_1330 d_343_869_1151_1276_1312_1331)
        TextBoxCons a_344_870_1152_1277_1314_1332 b_345_871_1153_1278_1315_1333 c_346_872_1154_1279_1316_1334 d_347_873_1155_1280_1317_1335 ->
            (TextBoxCons a_344_870_1152_1277_1314_1332 b_345_871_1153_1278_1315_1333 c_346_872_1154_1279_1316_1334 d_347_873_1155_1280_1317_1335)

_FUS_f_getSumHeights_f_computeHeightHzList_FUS_ :: HorizContainerList -> Int
_FUS_f_getSumHeights_f_computeHeightHzList_FUS_ inputTree_1349_1362 =
    case inputTree_1349_1362 of
        HorizContainerListInner elmList_307_833_1108_1336_1352_1363 remList_308_834_1109_1337_1353_1364 ->
            let maxH_326_852_1129_1345_1357_1367 :: Int = _FUS_f_getMaxHeight_f_computeHeightElmList_FUS_ elmList_307_833_1108_1336_1352_1363 in
            let fltAppE_1000_1130_1346_1358_1368 :: Int = _FUS_f_getSumHeights_f_computeHeightHzList_FUS_ remList_308_834_1109_1337_1353_1364 in
            addI maxH_326_852_1129_1345_1357_1367 fltAppE_1000_1130_1346_1358_1368
        HorizContainerListEnd elmList_311_837_1112_1340_1359_1369 ->
            _FUS_f_getMaxHeight_f_computeHeightElmList_FUS_ elmList_311_837_1112_1340_1359_1369

_FUS_f_getMaxHeight_f_computeHeightElmList_FUS_ :: ElementsList -> Int
_FUS_f_getMaxHeight_f_computeHeightElmList_FUS_ inputTree_1384_1397 =
    case inputTree_1384_1397 of
        ElementsListInner element_303_829_1101_1371_1387_1398 remList_304_830_1102_1372_1388_1399 ->
            let h1_320_846_1123_1380_1392_1402 :: Int = _FUS_f_getMaxHeight_f_computeHeightElmList_FUS_ remList_304_830_1102_1372_1388_1399 in
            let h2_321_847_1124_1381_1393_1403 :: Int = _FUS_f_getHeightElement_f_computeHeightElement_FUS_ element_303_829_1101_1371_1387_1398 in
            maxI h1_320_846_1123_1380_1392_1402 h2_321_847_1124_1381_1393_1403
        ElementsListEnd element_305_831_1105_1375_1394_1404 ->
            _FUS_f_getHeightElement_f_computeHeightElement_FUS_ element_305_831_1105_1375_1394_1404

_FUS_f_getHeightElement_f_computeHeightElement_FUS_ :: Element -> Int
_FUS_f_getHeightElement_f_computeHeightElement_FUS_ inputTree_1431_1451 =
    case inputTree_1431_1451 of
        VertContainer hzList_290_816_1087_1406_1435_1452_1464 nData_291_817_1088_1407_1436_1453_1465 ->
            _FUS_f_getSumHeights_f_computeHeightHzList_FUS_ hzList_290_816_1087_1406_1435_1452_1464
        ImageCons a_294_820_1092_1411_1441_1456_1467 b_295_821_1093_1412_1442_1457_1468 c_296_822_1094_1413_1443_1458_1469 d_297_823_1095_1414_1444_1459_1470 ->
            getHeight d_297_823_1095_1414_1444_1459_1470
        TextBoxCons a_298_824_1096_1415_1446_1460_1471 b_299_825_1097_1416_1447_1461_1472 c_300_826_1098_1417_1448_1462_1473 d_301_827_1099_1418_1449_1463_1474 ->
            getHeight d_301_827_1099_1418_1449_1463_1474

_FUS_f_updateHeight_f_updateWidth_FUS_ :: NodeData -> Int -> Int -> NodeData
_FUS_f_updateHeight_f_updateWidth_FUS_ inputTree_1491_1500 newWidth_401_927_1223_1482_1501 newHeight_393_919_1215_1490_1502 =
    case inputTree_1491_1500 of
        NodeDataK posX_402_928_1224_1475_1493_1503 posY_403_929_1225_1476_1494_1504 height_404_930_1226_1477_1495_1505 width_405_931_1227_1478_1496_1506 relWidth_406_932_1228_1479_1497_1507 fontStyle_407_933_1229_1480_1498_1508 ->
            (NodeDataK posX_402_928_1224_1475_1493_1503 posY_403_929_1225_1476_1494_1504 newHeight_393_919_1215_1490_1502 newWidth_401_927_1223_1482_1501 relWidth_406_932_1228_1479_1497_1507 fontStyle_407_933_1229_1480_1498_1508)

_FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ :: HorizContainerList -> Int
_FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ inputTree_1522_1535 =
    case inputTree_1522_1535 of
        HorizContainerListInner elmList_353_879_1164_1509_1525_1536 remList_354_880_1165_1510_1526_1537 ->
            let maxH_326_852_1129_1345_1357_1367_1518_1530_1540 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ elmList_353_879_1164_1509_1525_1536 in
            let fltAppE_1000_1130_1346_1358_1368_1519_1531_1541 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ remList_354_880_1165_1510_1526_1537 in
            addI maxH_326_852_1129_1345_1357_1367_1518_1530_1540 fltAppE_1000_1130_1346_1358_1368_1519_1531_1541
        HorizContainerListEnd elmList_355_881_1168_1513_1532_1542 ->
            _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ elmList_355_881_1168_1513_1532_1542

_FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ :: ElementsList -> Int
_FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ inputTree_1557_1570 =
    case inputTree_1557_1570 of
        ElementsListInner element_349_875_1157_1544_1560_1571 remList_350_876_1158_1545_1561_1572 ->
            let h1_320_846_1123_1380_1392_1402_1553_1565_1575 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ remList_350_876_1158_1545_1561_1572 in
            let h2_321_847_1124_1381_1393_1403_1554_1566_1576 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ element_349_875_1157_1544_1560_1571 in
            maxI h1_320_846_1123_1380_1392_1402_1553_1565_1575 h2_321_847_1124_1381_1393_1403_1554_1566_1576
        ElementsListEnd element_351_877_1161_1548_1567_1577 ->
            _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ element_351_877_1161_1548_1567_1577

_FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ :: Element -> Int
_FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ inputTree_1604_1624 =
    case inputTree_1604_1624 of
        VertContainer hzList_335_861_1143_1579_1608_1625_1637 nData_336_862_1144_1580_1609_1626_1638 ->
            _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ hzList_335_861_1143_1579_1608_1625_1637
        ImageCons a_340_866_1148_1584_1614_1629_1640 b_341_867_1149_1585_1615_1630_1641 c_342_868_1150_1586_1616_1631_1642 d_343_869_1151_1587_1617_1632_1643 ->
            getHeight d_343_869_1151_1587_1617_1632_1643
        TextBoxCons a_344_870_1152_1588_1619_1633_1644 b_345_871_1153_1589_1620_1634_1645 c_346_872_1154_1590_1621_1635_1646 d_347_873_1155_1591_1622_1636_1647 ->
            getHeight d_347_873_1155_1591_1622_1636_1647

_FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS_ :: HorizContainerList -> HorizContainerList
_FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS_ inputTree_1662_1676 =
    case inputTree_1662_1676 of
        HorizContainerListInner elmList_353_879_1164_1648_1665_1677 remList_354_880_1165_1649_1666_1678 ->
            let elmList__309_835_1110_1657_1670_1681 :: ElementsList = _FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS_ elmList_353_879_1164_1648_1665_1677 in
            let remList__310_836_1111_1658_1671_1682 :: HorizContainerList = _FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS_ remList_354_880_1165_1649_1666_1678 in
            (HorizContainerListInner elmList__309_835_1110_1657_1670_1681 remList__310_836_1111_1658_1671_1682)
        HorizContainerListEnd elmList_355_881_1168_1652_1672_1683 ->
            let fltPkd_998_1113_1660_1675_1685 :: ElementsList = _FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS_ elmList_355_881_1168_1652_1672_1683 in
            (HorizContainerListEnd fltPkd_998_1113_1660_1675_1685)

_FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS_ :: ElementsList -> ElementsList
_FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS_ inputTree_1700_1714 =
    case inputTree_1700_1714 of
        ElementsListInner element_349_875_1157_1686_1703_1715 remList_350_876_1158_1687_1704_1716 ->
            let fltPkd_995_1103_1695_1708_1719 :: Element = _FUS_f_computeHeightElement_f_resolveWidthElm_FUS_ element_349_875_1157_1686_1703_1715 in
            let fltPkd_996_1104_1696_1709_1720 :: ElementsList = _FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS_ remList_350_876_1158_1687_1704_1716 in
            (ElementsListInner fltPkd_995_1103_1695_1708_1719 fltPkd_996_1104_1696_1709_1720)
        ElementsListEnd element_351_877_1161_1690_1710_1721 ->
            let fltPkd_997_1106_1698_1713_1723 :: Element = _FUS_f_computeHeightElement_f_resolveWidthElm_FUS_ element_351_877_1161_1690_1710_1721 in
            (ElementsListEnd fltPkd_997_1106_1698_1713_1723)

_FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ :: HorizContainerList -> Int
_FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ inputTree_1737_1750 =
    case inputTree_1737_1750 of
        HorizContainerListInner elmList_353_879_1164_1724_1740_1751 remList_354_880_1165_1725_1741_1752 ->
            let fltAppE_1017_1195_1733_1745_1755 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ elmList_353_879_1164_1724_1740_1751 in
            let fltAppE_1018_1196_1734_1746_1756 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ remList_354_880_1165_1725_1741_1752 in
            maxI fltAppE_1017_1195_1733_1745_1755 fltAppE_1018_1196_1734_1746_1756
        HorizContainerListEnd elmList_355_881_1168_1728_1747_1757 ->
            _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ elmList_355_881_1168_1728_1747_1757

_FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ :: ElementsList -> Int
_FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ inputTree_1772_1785 =
    case inputTree_1772_1785 of
        ElementsListInner element_349_875_1157_1759_1775_1786 remList_350_876_1158_1760_1776_1787 ->
            let fltAppE_1015_1189_1768_1780_1790 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ element_349_875_1157_1759_1775_1786 in
            let fltAppE_1016_1190_1769_1781_1791 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ remList_350_876_1158_1760_1776_1787 in
            addI fltAppE_1015_1189_1768_1780_1790 fltAppE_1016_1190_1769_1781_1791
        ElementsListEnd element_351_877_1161_1763_1782_1792 ->
            _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ element_351_877_1161_1763_1782_1792

_FUS_f_getWidthElement_f_resolveWidthElm_FUS_ :: Element -> Int
_FUS_f_getWidthElement_f_resolveWidthElm_FUS_ inputTree_1819_1839 =
    case inputTree_1819_1839 of
        VertContainer hzList_335_861_1143_1794_1823_1840_1852 nData_336_862_1144_1795_1824_1841_1853 ->
            _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ hzList_335_861_1143_1794_1823_1840_1852
        ImageCons a_340_866_1148_1799_1829_1844_1855 b_341_867_1149_1800_1830_1845_1856 c_342_868_1150_1801_1831_1846_1857 d_343_869_1151_1802_1832_1847_1858 ->
            getWidth d_343_869_1151_1802_1832_1847_1858
        TextBoxCons a_344_870_1152_1803_1834_1848_1859 b_345_871_1153_1804_1835_1849_1860 c_346_872_1154_1805_1836_1850_1861 d_347_873_1155_1806_1837_1851_1862 ->
            getWidth d_347_873_1155_1806_1837_1851_1862

_FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ :: Element -> Int -> Int -> Element
_FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ inputTree_1898_1926 curX_247_773_1029_1896_1927 curY_248_774_1030_1897_1928 =
    case inputTree_1898_1926 of
        VertContainer hzList_335_861_1143_1268_1300_1320_1863_1902_1929 nData_336_862_1144_1269_1301_1321_1864_1903_1930 ->
            let tupled_output_2665 :: (Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ hzList_335_861_1143_1268_1300_1320_1863_1902_1929 curX_247_773_1029_1896_1927 curY_248_774_1030_1897_1928
                (tupled_output_2665_proj_0,tupled_output_2665_proj_1,tupled_output_2665_proj_2) :: (Int,Int,HorizContainerList) = tupled_output_2665 in
            let nData__252_778_1035_1882_1911_1937 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ nData_336_862_1144_1269_1301_1321_1864_1903_1930 tupled_output_2665_proj_1 tupled_output_2665_proj_0 curY_248_774_1030_1897_1928 curX_247_773_1029_1896_1927 in
            (VertContainer tupled_output_2665_proj_2 nData__252_778_1035_1882_1911_1937)
        ImageCons a_340_866_1148_1273_1309_1328_1869_1912_1938 b_341_867_1149_1274_1310_1329_1870_1913_1939 c_342_868_1150_1275_1311_1330_1871_1914_1940 d_343_869_1151_1276_1312_1331_1872_1915_1941 ->
            let fltPkd_980_1041_1888_1918_1943 :: NodeData = _FUS_f_updatePosX_f_updatePosY_FUS_ d_343_869_1151_1276_1312_1331_1872_1915_1941 curY_248_774_1030_1897_1928 curX_247_773_1029_1896_1927 in
            (ImageCons a_340_866_1148_1273_1309_1328_1869_1912_1938 b_341_867_1149_1274_1310_1329_1870_1913_1939 c_342_868_1150_1275_1311_1330_1871_1914_1940 fltPkd_980_1041_1888_1918_1943)
        TextBoxCons a_344_870_1152_1277_1314_1332_1873_1919_1944 b_345_871_1153_1278_1315_1333_1874_1920_1945 c_346_872_1154_1279_1316_1334_1875_1921_1946 d_347_873_1155_1280_1317_1335_1876_1922_1947 ->
            let fltPkd_982_1047_1894_1925_1949 :: NodeData = _FUS_f_updatePosX_f_updatePosY_FUS_ d_347_873_1155_1280_1317_1335_1876_1922_1947 curY_248_774_1030_1897_1928 curX_247_773_1029_1896_1927 in
            (TextBoxCons a_344_870_1152_1277_1314_1332_1873_1919_1944 b_345_871_1153_1278_1315_1333_1874_1920_1945 c_346_872_1154_1279_1316_1334_1875_1921_1946 fltPkd_982_1047_1894_1925_1949)

_FUS_f_updatePosX_f_updatePosY_FUS_ :: NodeData -> Int -> Int -> NodeData
_FUS_f_updatePosX_f_updatePosY_FUS_ inputTree_1966_1975 y_377_903_1199_1957_1976 x_385_911_1207_1965_1977 =
    case inputTree_1966_1975 of
        NodeDataK posX_378_904_1200_1950_1968_1978 posY_379_905_1201_1951_1969_1979 height_380_906_1202_1952_1970_1980 width_381_907_1203_1953_1971_1981 relWidth_382_908_1204_1954_1972_1982 fontStyle_383_909_1205_1955_1973_1983 ->
            (NodeDataK x_385_911_1207_1965_1977 y_377_903_1199_1957_1976 height_380_906_1202_1952_1970_1980 width_381_907_1203_1953_1971_1981 relWidth_382_908_1204_1954_1972_1982 fontStyle_383_909_1205_1955_1973_1983)

_FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ :: NodeData -> Int -> Int -> Int -> Int -> NodeData
_FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ inputTree_2002_2011 newWidth_401_927_1223_1482_1501_1991_2012 newHeight_393_919_1215_1490_1502_1992_2013 y_377_903_1199_1957_1976_2000_2014 x_385_911_1207_1965_1977_2001_2015 =
    case inputTree_2002_2011 of
        NodeDataK posX_402_928_1224_1475_1493_1503_1984_2004_2016 posY_403_929_1225_1476_1494_1504_1985_2005_2017 height_404_930_1226_1477_1495_1505_1986_2006_2018 width_405_931_1227_1478_1496_1506_1987_2007_2019 relWidth_406_932_1228_1479_1497_1507_1988_2008_2020 fontStyle_407_933_1229_1480_1498_1508_1989_2009_2021 ->
            (NodeDataK x_385_911_1207_1965_1977_2001_2015 y_377_903_1199_1957_1976_2000_2014 newHeight_393_919_1215_1490_1502_1992_2013 newWidth_401_927_1223_1482_1501_1991_2012 relWidth_406_932_1228_1479_1497_1507_1988_2008_2020 fontStyle_407_933_1229_1480_1498_1508_1989_2009_2021)

_FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ :: HorizContainerList -> Int -> Int -> HorizContainerList
_FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ inputTree_2040_2056 curX_271_797_1060_2038_2057 curY_272_798_1061_2039_2058 =
    case inputTree_2040_2056 of
        HorizContainerListInner elmList_353_879_1164_1648_1665_1677_2022_2043_2059 remList_354_880_1165_1649_1666_1678_2023_2044_2060 ->
            let tupled_output_2830 :: (ElementsList,Int) = _TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elmList_353_879_1164_1648_1665_1677_2022_2043_2059 curX_271_797_1060_2038_2057 curY_272_798_1061_2039_2058
                (tupled_output_2830_proj_0,tupled_output_2830_proj_1) :: (ElementsList,Int) = tupled_output_2830 in
            let fltAppE_986_1066_2033_2050_2065 :: Int = addI curY_272_798_1061_2039_2058 tupled_output_2830_proj_1 in
            let remList__277_803_1067_2034_2051_2066 :: HorizContainerList = _FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ remList_354_880_1165_1649_1666_1678_2023_2044_2060 curX_271_797_1060_2038_2057 fltAppE_986_1066_2033_2050_2065 in
            (HorizContainerListInner tupled_output_2830_proj_0 remList__277_803_1067_2034_2051_2066)
        HorizContainerListEnd elmList_355_881_1168_1652_1672_1683_2026_2052_2067 ->
            let fltPkd_987_1069_2036_2055_2069 :: ElementsList = _FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elmList_355_881_1168_1652_1672_1683_2026_2052_2067 curX_271_797_1060_2038_2057 curY_272_798_1061_2039_2058 in
            (HorizContainerListEnd fltPkd_987_1069_2036_2055_2069)

_FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ :: ElementsList -> Int -> Int -> ElementsList
_FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ inputTree_2088_2104 curX_262_788_1049_2086_2105 curY_263_789_1050_2087_2106 =
    case inputTree_2088_2104 of
        ElementsListInner element_349_875_1157_1686_1703_1715_2070_2091_2107 remList_350_876_1158_1687_1704_1716_2071_2092_2108 ->
            let tupled_output_3001 :: (Element,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ element_349_875_1157_1686_1703_1715_2070_2091_2107 curX_262_788_1049_2086_2105 curY_263_789_1050_2087_2106
                (tupled_output_3001_proj_0,tupled_output_3001_proj_1) :: (Element,Int) = tupled_output_3001 in
            let fltAppE_984_1055_2081_2098_2113 :: Int = addI curX_262_788_1049_2086_2105 tupled_output_3001_proj_1 in
            let remList__268_794_1056_2082_2099_2114 :: ElementsList = _FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ remList_350_876_1158_1687_1704_1716_2071_2092_2108 fltAppE_984_1055_2081_2098_2113 curY_263_789_1050_2087_2106 in
            (ElementsListInner tupled_output_3001_proj_0 remList__268_794_1056_2082_2099_2114)
        ElementsListEnd element_351_877_1161_1690_1710_1721_2074_2100_2115 ->
            let fltPkd_985_1058_2084_2103_2117 :: Element = _FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ element_351_877_1161_1690_1710_1721_2074_2100_2115 curX_262_788_1049_2086_2105 curY_263_789_1050_2087_2106 in
            (ElementsListEnd fltPkd_985_1058_2084_2103_2117)

_FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ :: Element -> Int
_FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ inputTree_2144_2165 =
    case inputTree_2144_2165 of
        VertContainer hzList_335_861_1143_1268_1300_1320_2118_2148_2166_2179 nData_336_862_1144_1269_1301_1321_2119_2149_2167_2180 ->
            _FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ hzList_335_861_1143_1268_1300_1320_2118_2148_2166_2179
        ImageCons a_340_866_1148_1273_1309_1328_2124_2155_2171_2182 b_341_867_1149_1274_1310_1329_2125_2156_2172_2183 c_342_868_1150_1275_1311_1330_2126_2157_2173_2184 d_343_869_1151_1276_1312_1331_2127_2158_2174_2185 ->
            getWidth d_343_869_1151_1276_1312_1331_2127_2158_2174_2185
        TextBoxCons a_344_870_1152_1277_1314_1332_2128_2160_2175_2186 b_345_871_1153_1278_1315_1333_2129_2161_2176_2187 c_346_872_1154_1279_1316_1334_2130_2162_2177_2188 d_347_873_1155_1280_1317_1335_2131_2163_2178_2189 ->
            getWidth d_347_873_1155_1280_1317_1335_2131_2163_2178_2189

_FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ :: HorizContainerList -> Int
_FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ inputTree_2203_2216 =
    case inputTree_2203_2216 of
        HorizContainerListInner elmList_353_879_1164_1648_1665_1677_2190_2206_2217 remList_354_880_1165_1649_1666_1678_2191_2207_2218 ->
            let fltAppE_1017_1195_2199_2211_2221 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elmList_353_879_1164_1648_1665_1677_2190_2206_2217 in
            let fltAppE_1018_1196_2200_2212_2222 :: Int = _FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ remList_354_880_1165_1649_1666_1678_2191_2207_2218 in
            maxI fltAppE_1017_1195_2199_2211_2221 fltAppE_1018_1196_2200_2212_2222
        HorizContainerListEnd elmList_355_881_1168_1652_1672_1683_2194_2213_2223 ->
            _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elmList_355_881_1168_1652_1672_1683_2194_2213_2223

_FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ :: ElementsList -> Int
_FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ inputTree_2238_2251 =
    case inputTree_2238_2251 of
        ElementsListInner element_349_875_1157_1686_1703_1715_2225_2241_2252 remList_350_876_1158_1687_1704_1716_2226_2242_2253 ->
            let fltAppE_1015_1189_2234_2246_2256 :: Int = _FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ element_349_875_1157_1686_1703_1715_2225_2241_2252 in
            let fltAppE_1016_1190_2235_2247_2257 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ remList_350_876_1158_1687_1704_1716_2226_2242_2253 in
            addI fltAppE_1015_1189_2234_2246_2256 fltAppE_1016_1190_2235_2247_2257
        ElementsListEnd element_351_877_1161_1690_1710_1721_2229_2248_2258 ->
            _FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ element_351_877_1161_1690_1710_1721_2229_2248_2258

_FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ :: ElementsList -> Int
_FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ inputTree_2273_2286 =
    case inputTree_2273_2286 of
        ElementsListInner element_349_875_1157_1686_1703_1715_2260_2276_2287 remList_350_876_1158_1687_1704_1716_2261_2277_2288 ->
            let h1_320_846_1123_2269_2281_2291 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ remList_350_876_1158_1687_1704_1716_2261_2277_2288 in
            let h2_321_847_1124_2270_2282_2292 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ element_349_875_1157_1686_1703_1715_2260_2276_2287 in
            maxI h1_320_846_1123_2269_2281_2291 h2_321_847_1124_2270_2282_2292
        ElementsListEnd element_351_877_1161_1690_1710_1721_2264_2283_2293 ->
            _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ element_351_877_1161_1690_1710_1721_2264_2283_2293

_FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ :: Element -> Int
_FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ inputTree_2321_2342 =
    case inputTree_2321_2342 of
        VertContainer hzList_335_861_1143_1268_1300_1320_2295_2325_2343_2356 nData_336_862_1144_1269_1301_1321_2296_2326_2344_2357 ->
            _FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ hzList_335_861_1143_1268_1300_1320_2295_2325_2343_2356
        ImageCons a_340_866_1148_1273_1309_1328_2301_2332_2348_2359 b_341_867_1149_1274_1310_1329_2302_2333_2349_2360 c_342_868_1150_1275_1311_1330_2303_2334_2350_2361 d_343_869_1151_1276_1312_1331_2304_2335_2351_2362 ->
            getHeight d_343_869_1151_1276_1312_1331_2304_2335_2351_2362
        TextBoxCons a_344_870_1152_1277_1314_1332_2305_2337_2352_2363 b_345_871_1153_1278_1315_1333_2306_2338_2353_2364 c_346_872_1154_1279_1316_1334_2307_2339_2354_2365 d_347_873_1155_1280_1317_1335_2308_2340_2355_2366 ->
            getHeight d_347_873_1155_1280_1317_1335_2308_2340_2355_2366

_FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ :: HorizContainerList -> Int
_FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ inputTree_2380_2393 =
    case inputTree_2380_2393 of
        HorizContainerListInner elmList_353_879_1164_1648_1665_1677_2367_2383_2394 remList_354_880_1165_1649_1666_1678_2368_2384_2395 ->
            let maxH_326_852_1129_2376_2388_2398 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elmList_353_879_1164_1648_1665_1677_2367_2383_2394 in
            let fltAppE_1000_1130_2377_2389_2399 :: Int = _FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ remList_354_880_1165_1649_1666_1678_2368_2384_2395 in
            addI maxH_326_852_1129_2376_2388_2398 fltAppE_1000_1130_2377_2389_2399
        HorizContainerListEnd elmList_355_881_1168_1652_1672_1683_2371_2390_2400 ->
            _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elmList_355_881_1168_1652_1672_1683_2371_2390_2400

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP_ :: HorizContainerList -> (Int,HorizContainerList,Int)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP_ input_2421_2438 =
    case input_2421_2438 of
        HorizContainerListInner horizcontainerlistinner0_2422 horizcontainerlistinner1_2423 ->
            let tupled_output_2477 :: (Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ horizcontainerlistinner0_2422
                (tupled_output_2477_proj_0,tupled_output_2477_proj_1,tupled_output_2477_proj_2) :: (Int,ElementsList,Int) = tupled_output_2477 in
            let tupled_output_2439 :: (Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP_ horizcontainerlistinner1_2423
                (tupled_output_2439_proj_0,tupled_output_2439_proj_1,tupled_output_2439_proj_2) :: (Int,HorizContainerList,Int) = tupled_output_2439 in
            let f0out0_2426 :: Int = addI tupled_output_2477_proj_0 tupled_output_2439_proj_0 in
            let f1out0_2429 :: HorizContainerList = (HorizContainerListInner tupled_output_2477_proj_1 tupled_output_2439_proj_1) in
            let f2out0_2432 :: Int = maxI tupled_output_2477_proj_2 tupled_output_2439_proj_2 in
            (f0out0_2426, f1out0_2429, f2out0_2432)
        HorizContainerListEnd horizcontainerlistend0_2433 ->
            let tupled_output_2515 :: (Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ horizcontainerlistend0_2433
                (tupled_output_2515_proj_0,tupled_output_2515_proj_1,tupled_output_2515_proj_2) :: (Int,ElementsList,Int) = tupled_output_2515 in
            let f1out0_2436 :: HorizContainerList = (HorizContainerListEnd tupled_output_2515_proj_1) in
            (tupled_output_2515_proj_0, f1out0_2436, tupled_output_2515_proj_2)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ :: ElementsList -> (Int,ElementsList,Int)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ input_2459_2476 =
    case input_2459_2476 of
        ElementsListInner elementslistinner0_2460 elementslistinner1_2461 ->
            let tupled_output_3161 :: (Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ elementslistinner1_2461
                (tupled_output_3161_proj_0,tupled_output_3161_proj_1,tupled_output_3161_proj_2) :: (Int,ElementsList,Int) = tupled_output_3161 in
            let tupled_output_3160 :: (Element,Int,Int) = _TUP__t__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__TUP_ elementslistinner0_2460
                (tupled_output_3160_proj_0,tupled_output_3160_proj_1,tupled_output_3160_proj_2) :: (Element,Int,Int) = tupled_output_3160 in
            let f0out0_2464 :: Int = maxI tupled_output_3161_proj_0 tupled_output_3160_proj_1 in
            let f1out0_2467 :: ElementsList = (ElementsListInner tupled_output_3160_proj_0 tupled_output_3161_proj_1) in
            let f2out0_2470 :: Int = addI tupled_output_3160_proj_2 tupled_output_3161_proj_2 in
            (f0out0_2464, f1out0_2467, f2out0_2470)
        ElementsListEnd elementslistend0_2471 ->
            let tupled_output_3320 :: (Element,Int,Int) = _TUP__t__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__TUP_ elementslistend0_2471
                (tupled_output_3320_proj_0,tupled_output_3320_proj_1,tupled_output_3320_proj_2) :: (Element,Int,Int) = tupled_output_3320 in
            let f1out0_2474 :: ElementsList = (ElementsListEnd tupled_output_3320_proj_0) in
            (tupled_output_3320_proj_1, f1out0_2474, tupled_output_3320_proj_2)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,HorizContainerList)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ input_2540_2559 curX_271_797_1060_2038_2057_2538_2560 curY_272_798_1061_2039_2058_2539_2561 =
    case input_2540_2559 of
        HorizContainerListInner horizcontainerlistinner0_2541 horizcontainerlistinner1_2542 ->
            let tupled_output_2618 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistinner0_2541 curX_271_797_1060_2038_2057_2538_2560 curY_272_798_1061_2039_2058_2539_2561
                (tupled_output_2618_proj_0,tupled_output_2618_proj_1,tupled_output_2618_proj_2,tupled_output_2618_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_2618 in
            let fltAppE_986_1066_2033_2050_2065_2533_2551 :: Int = addI curY_272_798_1061_2039_2058_2539_2561 tupled_output_2618_proj_3 in
            let tupled_output_2562 :: (Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_2542 curX_271_797_1060_2038_2057_2538_2560 fltAppE_986_1066_2033_2050_2065_2533_2551
                (tupled_output_2562_proj_0,tupled_output_2562_proj_1,tupled_output_2562_proj_2) :: (Int,Int,HorizContainerList) = tupled_output_2562 in
            let f0out0_2545 :: Int = addI tupled_output_2618_proj_0 tupled_output_2562_proj_0 in
            let f1out0_2548 :: Int = maxI tupled_output_2618_proj_1 tupled_output_2562_proj_1 in
            let f2out0_2553 :: HorizContainerList = (HorizContainerListInner tupled_output_2618_proj_2 tupled_output_2562_proj_2) in
            (f0out0_2545, f1out0_2548, f2out0_2553)
        HorizContainerListEnd horizcontainerlistend0_2554 ->
            let tupled_output_2664 :: (Int,Int,ElementsList) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_2554 curX_271_797_1060_2038_2057_2538_2560 curY_272_798_1061_2039_2058_2539_2561
                (tupled_output_2664_proj_0,tupled_output_2664_proj_1,tupled_output_2664_proj_2) :: (Int,Int,ElementsList) = tupled_output_2664 in
            let f2out0_2558 :: HorizContainerList = (HorizContainerListEnd tupled_output_2664_proj_2) in
            (tupled_output_2664_proj_0, tupled_output_2664_proj_1, f2out0_2558)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ :: ElementsList -> Int -> Int -> (Int,Int,ElementsList,Int)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ input_2592_2615 curX_262_788_1049_2086_2105_2584_2616 curY_263_789_1050_2087_2106_2585_2617 =
    case input_2592_2615 of
        ElementsListInner elementslistinner0_2593 elementslistinner1_2594 ->
            let tupled_output_3565 :: (Int,Int,Element,Int,Int) = _TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistinner0_2593 curX_262_788_1049_2086_2105_2584_2616 curY_263_789_1050_2087_2106_2585_2617
                (tupled_output_3565_proj_0,tupled_output_3565_proj_1,tupled_output_3565_proj_2,tupled_output_3565_proj_3,tupled_output_3565_proj_4) :: (Int,Int,Element,Int,Int) = tupled_output_3565 in
            let fltAppE_984_1055_2081_2098_2113_2579_2603 :: Int = addI curX_262_788_1049_2086_2105_2584_2616 tupled_output_3565_proj_3 in
            let tupled_output_3566 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elementslistinner1_2594 fltAppE_984_1055_2081_2098_2113_2579_2603 curY_263_789_1050_2087_2106_2585_2617
                (tupled_output_3566_proj_0,tupled_output_3566_proj_1,tupled_output_3566_proj_2,tupled_output_3566_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_3566 in
            let f0out0_2597 :: Int = maxI tupled_output_3566_proj_0 tupled_output_3565_proj_0 in
            let f1out0_2600 :: Int = addI tupled_output_3565_proj_1 tupled_output_3566_proj_1 in
            let f2out0_2605 :: ElementsList = (ElementsListInner tupled_output_3565_proj_2 tupled_output_3566_proj_2) in
            let f3out0_2608 :: Int = maxI tupled_output_3566_proj_3 tupled_output_3565_proj_4 in
            (f0out0_2597, f1out0_2600, f2out0_2605, f3out0_2608)
        ElementsListEnd elementslistend0_2609 ->
            let tupled_output_3787 :: (Int,Int,Element,Int) = _TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistend0_2609 curX_262_788_1049_2086_2105_2584_2616 curY_263_789_1050_2087_2106_2585_2617
                (tupled_output_3787_proj_0,tupled_output_3787_proj_1,tupled_output_3787_proj_2,tupled_output_3787_proj_3) :: (Int,Int,Element,Int) = tupled_output_3787 in
            let f2out0_2613 :: ElementsList = (ElementsListEnd tupled_output_3787_proj_2) in
            (tupled_output_3787_proj_0, tupled_output_3787_proj_1, f2out0_2613, tupled_output_3787_proj_3)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ :: ElementsList -> Int -> Int -> (Int,Int,ElementsList)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ input_2642_2661 curX_262_788_1049_2086_2105_2640_2662 curY_263_789_1050_2087_2106_2641_2663 =
    case input_2642_2661 of
        ElementsListInner elementslistinner0_2643 elementslistinner1_2644 ->
            let tupled_output_4008 :: (Int,Int,Element,Int) = _TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistinner0_2643 curX_262_788_1049_2086_2105_2640_2662 curY_263_789_1050_2087_2106_2641_2663
                (tupled_output_4008_proj_0,tupled_output_4008_proj_1,tupled_output_4008_proj_2,tupled_output_4008_proj_3) :: (Int,Int,Element,Int) = tupled_output_4008 in
            let fltAppE_984_1055_2081_2098_2113_2635_2653 :: Int = addI curX_262_788_1049_2086_2105_2640_2662 tupled_output_4008_proj_3 in
            let tupled_output_4009 :: (Int,Int,ElementsList) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elementslistinner1_2644 fltAppE_984_1055_2081_2098_2113_2635_2653 curY_263_789_1050_2087_2106_2641_2663
                (tupled_output_4009_proj_0,tupled_output_4009_proj_1,tupled_output_4009_proj_2) :: (Int,Int,ElementsList) = tupled_output_4009 in
            let f0out0_2647 :: Int = maxI tupled_output_4009_proj_0 tupled_output_4008_proj_0 in
            let f1out0_2650 :: Int = addI tupled_output_4008_proj_1 tupled_output_4009_proj_1 in
            let f2out0_2655 :: ElementsList = (ElementsListInner tupled_output_4008_proj_2 tupled_output_4009_proj_2) in
            (f0out0_2647, f1out0_2650, f2out0_2655)
        ElementsListEnd elementslistend0_2656 ->
            let tupled_output_4206 :: (Int,Int,Element) = _TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistend0_2656 curX_262_788_1049_2086_2105_2640_2662 curY_263_789_1050_2087_2106_2641_2663
                (tupled_output_4206_proj_0,tupled_output_4206_proj_1,tupled_output_4206_proj_2) :: (Int,Int,Element) = tupled_output_4206 in
            let f2out0_2660 :: ElementsList = (ElementsListEnd tupled_output_4206_proj_2) in
            (tupled_output_4206_proj_0, tupled_output_4206_proj_1, f2out0_2660)

_TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ :: ElementsList -> Int -> Int -> (ElementsList,Int)
_TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ input_2683_2698 curX_262_788_1049_2086_2105_2675_2699 curY_263_789_1050_2087_2106_2676_2700 =
    case input_2683_2698 of
        ElementsListInner elementslistinner0_2684 elementslistinner1_2685 ->
            let tupled_output_2771 :: (Element,Int,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistinner0_2684 curX_262_788_1049_2086_2105_2675_2699 curY_263_789_1050_2087_2106_2676_2700
                (tupled_output_2771_proj_0,tupled_output_2771_proj_1,tupled_output_2771_proj_2) :: (Element,Int,Int) = tupled_output_2771 in
            let fltAppE_984_1055_2081_2098_2113_2670_2688 :: Int = addI curX_262_788_1049_2086_2105_2675_2699 tupled_output_2771_proj_1 in
            let tupled_output_2772 :: (ElementsList,Int) = _TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elementslistinner1_2685 fltAppE_984_1055_2081_2098_2113_2670_2688 curY_263_789_1050_2087_2106_2676_2700
                (tupled_output_2772_proj_0,tupled_output_2772_proj_1) :: (ElementsList,Int) = tupled_output_2772 in
            let f0out0_2690 :: ElementsList = (ElementsListInner tupled_output_2771_proj_0 tupled_output_2772_proj_0) in
            let f1out0_2693 :: Int = maxI tupled_output_2772_proj_1 tupled_output_2771_proj_2 in
            (f0out0_2690, f1out0_2693)
        ElementsListEnd elementslistend0_2694 ->
            let tupled_output_2829 :: (Element,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistend0_2694 curX_262_788_1049_2086_2105_2675_2699 curY_263_789_1050_2087_2106_2676_2700
                (tupled_output_2829_proj_0,tupled_output_2829_proj_1) :: (Element,Int) = tupled_output_2829 in
            let f0out0_2696 :: ElementsList = (ElementsListEnd tupled_output_2829_proj_0) in
            (f0out0_2696, tupled_output_2829_proj_1)

_TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Element,Int,Int)
_TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_2742_2768 curX_247_773_1029_1896_1927_2718_2769 curY_248_774_1030_1897_1928_2719_2770 =
    case input_2742_2768 of
        ImageCons imagecons0_2743 imagecons1_2744 imagecons2_2745 imagecons3_2746 ->
            let tupled_output_4243 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_2746 curY_248_774_1030_1897_1928_2719_2770 curX_247_773_1029_1896_1927_2718_2769
                (tupled_output_4243_proj_0,tupled_output_4243_proj_1,tupled_output_4243_proj_2) :: (Int,Int,NodeData) = tupled_output_4243 in
            let f0out0_2748 :: Element = (ImageCons imagecons0_2743 imagecons1_2744 imagecons2_2745 tupled_output_4243_proj_2) in
            (f0out0_2748, tupled_output_4243_proj_1, tupled_output_4243_proj_0)
        TextBoxCons textboxcons0_2751 textboxcons1_2752 textboxcons2_2753 textboxcons3_2754 ->
            let tupled_output_4280 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_2754 curY_248_774_1030_1897_1928_2719_2770 curX_247_773_1029_1896_1927_2718_2769
                (tupled_output_4280_proj_0,tupled_output_4280_proj_1,tupled_output_4280_proj_2) :: (Int,Int,NodeData) = tupled_output_4280 in
            let f0out0_2756 :: Element = (TextBoxCons textboxcons0_2751 textboxcons1_2752 textboxcons2_2753 tupled_output_4280_proj_2) in
            (f0out0_2756, tupled_output_4280_proj_1, tupled_output_4280_proj_0)
        VertContainer vertcontainer0_2759 vertcontainer1_2760 ->
            let tupled_output_4481 :: (Int,Int,HorizContainerList,Int,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ vertcontainer0_2759 curX_247_773_1029_1896_1927_2718_2769 curY_248_774_1030_1897_1928_2719_2770
                (tupled_output_4481_proj_0,tupled_output_4481_proj_1,tupled_output_4481_proj_2,tupled_output_4481_proj_3,tupled_output_4481_proj_4) :: (Int,Int,HorizContainerList,Int,Int) = tupled_output_4481 in
            let nData__252_778_1035_1882_1911_1937_2706_2764 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_2760 tupled_output_4481_proj_1 tupled_output_4481_proj_0 curY_248_774_1030_1897_1928_2719_2770 curX_247_773_1029_1896_1927_2718_2769 in
            let f0out0_2765 :: Element = (VertContainer tupled_output_4481_proj_2 nData__252_778_1035_1882_1911_1937_2706_2764) in
            (f0out0_2765, tupled_output_4481_proj_3, tupled_output_4481_proj_4)

_TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Element,Int)
_TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_2803_2826 curX_247_773_1029_1896_1927_2790_2827 curY_248_774_1030_1897_1928_2791_2828 =
    case input_2803_2826 of
        ImageCons imagecons0_2804 imagecons1_2805 imagecons2_2806 imagecons3_2807 ->
            let tupled_output_4510 :: (Int,NodeData) = _TUP__t_getHeight_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_2807 curY_248_774_1030_1897_1928_2791_2828 curX_247_773_1029_1896_1927_2790_2827
                (tupled_output_4510_proj_0,tupled_output_4510_proj_1) :: (Int,NodeData) = tupled_output_4510 in
            let f0out0_2809 :: Element = (ImageCons imagecons0_2804 imagecons1_2805 imagecons2_2806 tupled_output_4510_proj_1) in
            (f0out0_2809, tupled_output_4510_proj_0)
        TextBoxCons textboxcons0_2811 textboxcons1_2812 textboxcons2_2813 textboxcons3_2814 ->
            let tupled_output_4539 :: (Int,NodeData) = _TUP__t_getHeight_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_2814 curY_248_774_1030_1897_1928_2791_2828 curX_247_773_1029_1896_1927_2790_2827
                (tupled_output_4539_proj_0,tupled_output_4539_proj_1) :: (Int,NodeData) = tupled_output_4539 in
            let f0out0_2816 :: Element = (TextBoxCons textboxcons0_2811 textboxcons1_2812 textboxcons2_2813 tupled_output_4539_proj_1) in
            (f0out0_2816, tupled_output_4539_proj_0)
        VertContainer vertcontainer0_2818 vertcontainer1_2819 ->
            let tupled_output_4657 :: (Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ vertcontainer0_2818 curX_247_773_1029_1896_1927_2790_2827 curY_248_774_1030_1897_1928_2791_2828
                (tupled_output_4657_proj_0,tupled_output_4657_proj_1,tupled_output_4657_proj_2,tupled_output_4657_proj_3) :: (Int,Int,HorizContainerList,Int) = tupled_output_4657 in
            let nData__252_778_1035_1882_1911_1937_2778_2823 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_2819 tupled_output_4657_proj_1 tupled_output_4657_proj_0 curY_248_774_1030_1897_1928_2791_2828 curX_247_773_1029_1896_1927_2790_2827 in
            let f0out0_2824 :: Element = (VertContainer tupled_output_4657_proj_2 nData__252_778_1035_1882_1911_1937_2778_2823) in
            (f0out0_2824, tupled_output_4657_proj_3)

_TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Element,Int)
_TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_2861_2884 curX_247_773_1029_1896_1927_2848_2885 curY_248_774_1030_1897_1928_2849_2886 =
    case input_2861_2884 of
        ImageCons imagecons0_2862 imagecons1_2863 imagecons2_2864 imagecons3_2865 ->
            let tupled_output_2915 :: (Int,NodeData) = _TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_2865 curY_248_774_1030_1897_1928_2849_2886 curX_247_773_1029_1896_1927_2848_2885
                (tupled_output_2915_proj_0,tupled_output_2915_proj_1) :: (Int,NodeData) = tupled_output_2915 in
            let f0out0_2867 :: Element = (ImageCons imagecons0_2862 imagecons1_2863 imagecons2_2864 tupled_output_2915_proj_1) in
            (f0out0_2867, tupled_output_2915_proj_0)
        TextBoxCons textboxcons0_2869 textboxcons1_2870 textboxcons2_2871 textboxcons3_2872 ->
            let tupled_output_2944 :: (Int,NodeData) = _TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_2872 curY_248_774_1030_1897_1928_2849_2886 curX_247_773_1029_1896_1927_2848_2885
                (tupled_output_2944_proj_0,tupled_output_2944_proj_1) :: (Int,NodeData) = tupled_output_2944 in
            let f0out0_2874 :: Element = (TextBoxCons textboxcons0_2869 textboxcons1_2870 textboxcons2_2871 tupled_output_2944_proj_1) in
            (f0out0_2874, tupled_output_2944_proj_0)
        VertContainer vertcontainer0_2876 vertcontainer1_2877 ->
            let tupled_output_3000 :: (Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ vertcontainer0_2876 curX_247_773_1029_1896_1927_2848_2885 curY_248_774_1030_1897_1928_2849_2886
                (tupled_output_3000_proj_0,tupled_output_3000_proj_1,tupled_output_3000_proj_2,tupled_output_3000_proj_3) :: (Int,Int,HorizContainerList,Int) = tupled_output_3000 in
            let nData__252_778_1035_1882_1911_1937_2836_2881 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_2877 tupled_output_3000_proj_1 tupled_output_3000_proj_0 curY_248_774_1030_1897_1928_2849_2886 curX_247_773_1029_1896_1927_2848_2885 in
            let f0out0_2882 :: Element = (VertContainer tupled_output_3000_proj_2 nData__252_778_1035_1882_1911_1937_2836_2881) in
            (f0out0_2882, tupled_output_3000_proj_3)

_TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ :: NodeData -> Int -> Int -> (Int,NodeData)
_TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ input_2903_2912 y_377_903_1199_1957_1976_2901_2913 x_385_911_1207_1965_1977_2902_2914 =
    case input_2903_2912 of
        NodeDataK nodedatak0_2904 nodedatak1_2905 nodedatak2_2906 nodedatak3_2907 nodedatak4_2908 nodedatak5_2909 ->
            let f1out0_2911 :: NodeData = (NodeDataK x_385_911_1207_1965_1977_2902_2914 y_377_903_1199_1957_1976_2901_2913 nodedatak2_2906 nodedatak3_2907 nodedatak4_2908 nodedatak5_2909) in
            (nodedatak3_2907, f1out0_2911)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,HorizContainerList,Int)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ input_2974_2997 curX_271_797_1060_2038_2057_2966_2998 curY_272_798_1061_2039_2058_2967_2999 =
    case input_2974_2997 of
        HorizContainerListInner horizcontainerlistinner0_2975 horizcontainerlistinner1_2976 ->
            let tupled_output_4921 :: (Int,Int,ElementsList,Int,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistinner0_2975 curX_271_797_1060_2038_2057_2966_2998 curY_272_798_1061_2039_2058_2967_2999
                (tupled_output_4921_proj_0,tupled_output_4921_proj_1,tupled_output_4921_proj_2,tupled_output_4921_proj_3,tupled_output_4921_proj_4) :: (Int,Int,ElementsList,Int,Int) = tupled_output_4921 in
            let fltAppE_986_1066_2033_2050_2065_2961_2985 :: Int = addI curY_272_798_1061_2039_2058_2967_2999 tupled_output_4921_proj_4 in
            let tupled_output_4922 :: (Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_2976 curX_271_797_1060_2038_2057_2966_2998 fltAppE_986_1066_2033_2050_2065_2961_2985
                (tupled_output_4922_proj_0,tupled_output_4922_proj_1,tupled_output_4922_proj_2,tupled_output_4922_proj_3) :: (Int,Int,HorizContainerList,Int) = tupled_output_4922 in
            let f0out0_2979 :: Int = addI tupled_output_4921_proj_0 tupled_output_4922_proj_0 in
            let f1out0_2982 :: Int = maxI tupled_output_4921_proj_1 tupled_output_4922_proj_1 in
            let f2out0_2987 :: HorizContainerList = (HorizContainerListInner tupled_output_4921_proj_2 tupled_output_4922_proj_2) in
            let f3out0_2990 :: Int = maxI tupled_output_4921_proj_3 tupled_output_4922_proj_3 in
            (f0out0_2979, f1out0_2982, f2out0_2987, f3out0_2990)
        HorizContainerListEnd horizcontainerlistend0_2991 ->
            let tupled_output_5148 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_2991 curX_271_797_1060_2038_2057_2966_2998 curY_272_798_1061_2039_2058_2967_2999
                (tupled_output_5148_proj_0,tupled_output_5148_proj_1,tupled_output_5148_proj_2,tupled_output_5148_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_5148 in
            let f2out0_2995 :: HorizContainerList = (HorizContainerListEnd tupled_output_5148_proj_2) in
            (tupled_output_5148_proj_0, tupled_output_5148_proj_1, f2out0_2995, tupled_output_5148_proj_3)

_TUP__t__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__TUP_ :: Element -> (Element,Int,Int)
_TUP__t__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__TUP_ input_3037_3059 =
    case input_3037_3059 of
        ImageCons imagecons0_3038 imagecons1_3039 imagecons2_3040 imagecons3_3041 ->
            let f0out0_3042 :: Element = (ImageCons imagecons0_3038 imagecons1_3039 imagecons2_3040 imagecons3_3041) in
            let tupled_output_3084 :: (Int,Int) = _TUP__t_getHeight_t_getWidth_TUP_ imagecons3_3041
                (tupled_output_3084_proj_0,tupled_output_3084_proj_1) :: (Int,Int) = tupled_output_3084 in
            (f0out0_3042, tupled_output_3084_proj_0, tupled_output_3084_proj_1)
        TextBoxCons textboxcons0_3045 textboxcons1_3046 textboxcons2_3047 textboxcons3_3048 ->
            let f0out0_3049 :: Element = (TextBoxCons textboxcons0_3045 textboxcons1_3046 textboxcons2_3047 textboxcons3_3048) in
            let tupled_output_3109 :: (Int,Int) = _TUP__t_getHeight_t_getWidth_TUP_ textboxcons3_3048
                (tupled_output_3109_proj_0,tupled_output_3109_proj_1) :: (Int,Int) = tupled_output_3109 in
            (f0out0_3049, tupled_output_3109_proj_0, tupled_output_3109_proj_1)
        VertContainer vertcontainer0_3052 vertcontainer1_3053 ->
            let tupled_output_3159 :: (Int,Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP__TUP_ vertcontainer0_3052
                (tupled_output_3159_proj_0,tupled_output_3159_proj_1,tupled_output_3159_proj_2,tupled_output_3159_proj_3,tupled_output_3159_proj_4) :: (Int,Int,Int,HorizContainerList,Int) = tupled_output_3159 in
            let fltPkd_994_1091_1286_1308_1327_3005_3055 :: NodeData = _FUS_f_updateHeight_f_updateWidth_FUS_ vertcontainer1_3053 tupled_output_3159_proj_4 tupled_output_3159_proj_2 in
            let f0out0_3056 :: Element = (VertContainer tupled_output_3159_proj_3 fltPkd_994_1091_1286_1308_1327_3005_3055) in
            (f0out0_3056, tupled_output_3159_proj_0, tupled_output_3159_proj_1)

_TUP__t_getHeight_t_getWidth_TUP_ :: NodeData -> (Int,Int)
_TUP__t_getHeight_t_getWidth_TUP_ input_3074_3083 =
    case input_3074_3083 of
        NodeDataK nodedatak0_3075 nodedatak1_3076 nodedatak2_3077 nodedatak3_3078 nodedatak4_3079 nodedatak5_3080 ->
            (nodedatak2_3077, nodedatak3_3078)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP__TUP_ :: HorizContainerList -> (Int,Int,Int,HorizContainerList,Int)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP__TUP_ input_3133_3158 =
    case input_3133_3158 of
        HorizContainerListInner horizcontainerlistinner0_3134 horizcontainerlistinner1_3135 ->
            let maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3112_3136 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3134 in
            let fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3113_3137 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3135 in
            let f0out0_3138 :: Int = addI maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3112_3136 fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3113_3137 in
            let fltAppE_1017_1195_1733_1745_1755_3118_3139 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3134 in
            let fltAppE_1018_1196_1734_1746_1756_3119_3140 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3135 in
            let f1out0_3141 :: Int = maxI fltAppE_1017_1195_1733_1745_1755_3118_3139 fltAppE_1018_1196_1734_1746_1756_3119_3140 in
            let tupled_output_2477_3124_3142 :: (Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ horizcontainerlistinner0_3134
                (tupled_output_2477_3124_3142_proj_0,tupled_output_2477_3124_3142_proj_1,tupled_output_2477_3124_3142_proj_2) :: (Int,ElementsList,Int) = tupled_output_2477_3124_3142 in
            let tupled_output_2439_3125_3143 :: (Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__TUP_ horizcontainerlistinner1_3135
                (tupled_output_2439_3125_3143_proj_0,tupled_output_2439_3125_3143_proj_1,tupled_output_2439_3125_3143_proj_2) :: (Int,HorizContainerList,Int) = tupled_output_2439_3125_3143 in
            let f0out0_2426_3126_3144 :: Int = addI tupled_output_2477_3124_3142_proj_0 tupled_output_2439_3125_3143_proj_0 in
            let f1out0_2429_3127_3145 :: HorizContainerList = (HorizContainerListInner tupled_output_2477_3124_3142_proj_1 tupled_output_2439_3125_3143_proj_1) in
            let f2out0_2432_3128_3146 :: Int = maxI tupled_output_2477_3124_3142_proj_2 tupled_output_2439_3125_3143_proj_2 in
            (f0out0_3138, f1out0_3141, f0out0_2426_3126_3144, f1out0_2429_3127_3145, f2out0_2432_3128_3146)
        HorizContainerListEnd horizcontainerlistend0_3150 ->
            let f0out0_3151 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistend0_3150 in
            let f1out0_3152 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistend0_3150 in
            let tupled_output_2515_3130_3153 :: (Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__TUP_ horizcontainerlistend0_3150
                (tupled_output_2515_3130_3153_proj_0,tupled_output_2515_3130_3153_proj_1,tupled_output_2515_3130_3153_proj_2) :: (Int,ElementsList,Int) = tupled_output_2515_3130_3153 in
            let f1out0_2436_3131_3154 :: HorizContainerList = (HorizContainerListEnd tupled_output_2515_3130_3153_proj_1) in
            (f0out0_3151, f1out0_3152, tupled_output_2515_3130_3153_proj_0, f1out0_2436_3131_3154, tupled_output_2515_3130_3153_proj_2)

_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Int,Int,Element,Int,Int)
_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_3382_3412 curX_247_773_1029_1896_1927_3358_3413 curY_248_774_1030_1897_1928_3359_3414 =
    case input_3382_3412 of
        ImageCons imagecons0_3383 imagecons1_3384 imagecons2_3385 imagecons3_3386 ->
            let tupled_output_3451 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_3386 curY_248_774_1030_1897_1928_3359_3414 curX_247_773_1029_1896_1927_3358_3413
                (tupled_output_3451_proj_0,tupled_output_3451_proj_1,tupled_output_3451_proj_2) :: (Int,Int,NodeData) = tupled_output_3451 in
            let f2out0_3390 :: Element = (ImageCons imagecons0_3383 imagecons1_3384 imagecons2_3385 tupled_output_3451_proj_2) in
            (tupled_output_3451_proj_0, tupled_output_3451_proj_1, f2out0_3390, tupled_output_3451_proj_1, tupled_output_3451_proj_0)
        TextBoxCons textboxcons0_3393 textboxcons1_3394 textboxcons2_3395 textboxcons3_3396 ->
            let tupled_output_3488 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_3396 curY_248_774_1030_1897_1928_3359_3414 curX_247_773_1029_1896_1927_3358_3413
                (tupled_output_3488_proj_0,tupled_output_3488_proj_1,tupled_output_3488_proj_2) :: (Int,Int,NodeData) = tupled_output_3488 in
            let f2out0_3400 :: Element = (TextBoxCons textboxcons0_3393 textboxcons1_3394 textboxcons2_3395 tupled_output_3488_proj_2) in
            (tupled_output_3488_proj_0, tupled_output_3488_proj_1, f2out0_3400, tupled_output_3488_proj_1, tupled_output_3488_proj_0)
        VertContainer vertcontainer0_3403 vertcontainer1_3404 ->
            let tupled_output_3564 :: (Int,Int,Int,Int,Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ vertcontainer0_3403 curX_247_773_1029_1896_1927_3358_3413 curY_248_774_1030_1897_1928_3359_3414
                (tupled_output_3564_proj_0,tupled_output_3564_proj_1,tupled_output_3564_proj_2,tupled_output_3564_proj_3,tupled_output_3564_proj_4,tupled_output_3564_proj_5,tupled_output_3564_proj_6) :: (Int,Int,Int,Int,Int,Int,HorizContainerList) = tupled_output_3564 in
            let nData__252_778_1035_1882_1911_1937_3346_3408 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_3404 tupled_output_3564_proj_5 tupled_output_3564_proj_4 curY_248_774_1030_1897_1928_3359_3414 curX_247_773_1029_1896_1927_3358_3413 in
            let f2out0_3409 :: Element = (VertContainer tupled_output_3564_proj_6 nData__252_778_1035_1882_1911_1937_3346_3408) in
            (tupled_output_3564_proj_0, tupled_output_3564_proj_1, f2out0_3409, tupled_output_3564_proj_2, tupled_output_3564_proj_3)

_TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ :: NodeData -> Int -> Int -> (Int,Int,NodeData)
_TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ input_3438_3448 y_377_903_1199_1957_1976_3436_3449 x_385_911_1207_1965_1977_3437_3450 =
    case input_3438_3448 of
        NodeDataK nodedatak0_3439 nodedatak1_3440 nodedatak2_3441 nodedatak3_3442 nodedatak4_3443 nodedatak5_3444 ->
            let f2out0_3447 :: NodeData = (NodeDataK x_385_911_1207_1965_1977_3437_3450 y_377_903_1199_1957_1976_3436_3449 nodedatak2_3441 nodedatak3_3442 nodedatak4_3443 nodedatak5_3444) in
            (nodedatak2_3441, nodedatak3_3442, f2out0_3447)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,Int,Int,Int,Int,HorizContainerList)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ input_3527_3561 curX_271_797_1060_2038_2057_2538_2560_3525_3562 curY_272_798_1061_2039_2058_2539_2561_3526_3563 =
    case input_3527_3561 of
        HorizContainerListInner horizcontainerlistinner0_3528 horizcontainerlistinner1_3529 ->
            let maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3491_3530 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3528 in
            let fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3492_3531 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3529 in
            let f0out0_3532 :: Int = addI maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3491_3530 fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3492_3531 in
            let fltAppE_1017_1195_1733_1745_1755_3497_3533 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3528 in
            let fltAppE_1018_1196_1734_1746_1756_3498_3534 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3529 in
            let f1out0_3535 :: Int = maxI fltAppE_1017_1195_1733_1745_1755_3497_3533 fltAppE_1018_1196_1734_1746_1756_3498_3534 in
            let fltAppE_1017_1195_2199_2211_2221_3503_3536 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistinner0_3528 in
            let fltAppE_1018_1196_2200_2212_2222_3504_3537 :: Int = _FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ horizcontainerlistinner1_3529 in
            let f2out0_3538 :: Int = maxI fltAppE_1017_1195_2199_2211_2221_3503_3536 fltAppE_1018_1196_2200_2212_2222_3504_3537 in
            let maxH_326_852_1129_2376_2388_2398_3509_3539 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistinner0_3528 in
            let fltAppE_1000_1130_2377_2389_2399_3510_3540 :: Int = _FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ horizcontainerlistinner1_3529 in
            let f3out0_3541 :: Int = addI maxH_326_852_1129_2376_2388_2398_3509_3539 fltAppE_1000_1130_2377_2389_2399_3510_3540 in
            let tupled_output_2618_3515_3542 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistinner0_3528 curX_271_797_1060_2038_2057_2538_2560_3525_3562 curY_272_798_1061_2039_2058_2539_2561_3526_3563
                (tupled_output_2618_3515_3542_proj_0,tupled_output_2618_3515_3542_proj_1,tupled_output_2618_3515_3542_proj_2,tupled_output_2618_3515_3542_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_2618_3515_3542 in
            let fltAppE_986_1066_2033_2050_2065_2533_2551_3516_3543 :: Int = addI curY_272_798_1061_2039_2058_2539_2561_3526_3563 tupled_output_2618_3515_3542_proj_3 in
            let tupled_output_2562_3517_3544 :: (Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_3529 curX_271_797_1060_2038_2057_2538_2560_3525_3562 fltAppE_986_1066_2033_2050_2065_2533_2551_3516_3543
                (tupled_output_2562_3517_3544_proj_0,tupled_output_2562_3517_3544_proj_1,tupled_output_2562_3517_3544_proj_2) :: (Int,Int,HorizContainerList) = tupled_output_2562_3517_3544 in
            let f0out0_2545_3518_3545 :: Int = addI tupled_output_2618_3515_3542_proj_0 tupled_output_2562_3517_3544_proj_0 in
            let f1out0_2548_3519_3546 :: Int = maxI tupled_output_2618_3515_3542_proj_1 tupled_output_2562_3517_3544_proj_1 in
            let f2out0_2553_3520_3547 :: HorizContainerList = (HorizContainerListInner tupled_output_2618_3515_3542_proj_2 tupled_output_2562_3517_3544_proj_2) in
            (f0out0_3532, f1out0_3535, f2out0_3538, f3out0_3541, f0out0_2545_3518_3545, f1out0_2548_3519_3546, f2out0_2553_3520_3547)
        HorizContainerListEnd horizcontainerlistend0_3551 ->
            let f0out0_3552 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistend0_3551 in
            let f1out0_3553 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistend0_3551 in
            let f2out0_3554 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistend0_3551 in
            let f3out0_3555 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistend0_3551 in
            let tupled_output_2664_3522_3556 :: (Int,Int,ElementsList) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_3551 curX_271_797_1060_2038_2057_2538_2560_3525_3562 curY_272_798_1061_2039_2058_2539_2561_3526_3563
                (tupled_output_2664_3522_3556_proj_0,tupled_output_2664_3522_3556_proj_1,tupled_output_2664_3522_3556_proj_2) :: (Int,Int,ElementsList) = tupled_output_2664_3522_3556 in
            let f2out0_2558_3523_3557 :: HorizContainerList = (HorizContainerListEnd tupled_output_2664_3522_3556_proj_2) in
            (f0out0_3552, f1out0_3553, f2out0_3554, f3out0_3555, tupled_output_2664_3522_3556_proj_0, tupled_output_2664_3522_3556_proj_1, f2out0_2558_3523_3557)

_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Int,Int,Element,Int)
_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_3617_3644 curX_247_773_1029_1896_1927_3604_3645 curY_248_774_1030_1897_1928_3605_3646 =
    case input_3617_3644 of
        ImageCons imagecons0_3618 imagecons1_3619 imagecons2_3620 imagecons3_3621 ->
            let tupled_output_3683 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_3621 curY_248_774_1030_1897_1928_3605_3646 curX_247_773_1029_1896_1927_3604_3645
                (tupled_output_3683_proj_0,tupled_output_3683_proj_1,tupled_output_3683_proj_2) :: (Int,Int,NodeData) = tupled_output_3683 in
            let f2out0_3625 :: Element = (ImageCons imagecons0_3618 imagecons1_3619 imagecons2_3620 tupled_output_3683_proj_2) in
            (tupled_output_3683_proj_0, tupled_output_3683_proj_1, f2out0_3625, tupled_output_3683_proj_0)
        TextBoxCons textboxcons0_3627 textboxcons1_3628 textboxcons2_3629 textboxcons3_3630 ->
            let tupled_output_3720 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_3630 curY_248_774_1030_1897_1928_3605_3646 curX_247_773_1029_1896_1927_3604_3645
                (tupled_output_3720_proj_0,tupled_output_3720_proj_1,tupled_output_3720_proj_2) :: (Int,Int,NodeData) = tupled_output_3720 in
            let f2out0_3634 :: Element = (TextBoxCons textboxcons0_3627 textboxcons1_3628 textboxcons2_3629 tupled_output_3720_proj_2) in
            (tupled_output_3720_proj_0, tupled_output_3720_proj_1, f2out0_3634, tupled_output_3720_proj_0)
        VertContainer vertcontainer0_3636 vertcontainer1_3637 ->
            let tupled_output_3786 :: (Int,Int,Int,Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ vertcontainer0_3636 curX_247_773_1029_1896_1927_3604_3645 curY_248_774_1030_1897_1928_3605_3646
                (tupled_output_3786_proj_0,tupled_output_3786_proj_1,tupled_output_3786_proj_2,tupled_output_3786_proj_3,tupled_output_3786_proj_4,tupled_output_3786_proj_5) :: (Int,Int,Int,Int,Int,HorizContainerList) = tupled_output_3786 in
            let nData__252_778_1035_1882_1911_1937_3592_3641 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_3637 tupled_output_3786_proj_4 tupled_output_3786_proj_3 curY_248_774_1030_1897_1928_3605_3646 curX_247_773_1029_1896_1927_3604_3645 in
            let f2out0_3642 :: Element = (VertContainer tupled_output_3786_proj_5 nData__252_778_1035_1882_1911_1937_3592_3641) in
            (tupled_output_3786_proj_0, tupled_output_3786_proj_1, f2out0_3642, tupled_output_3786_proj_2)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,Int,Int,Int,HorizContainerList)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ input_3753_3783 curX_271_797_1060_2038_2057_2538_2560_3751_3784 curY_272_798_1061_2039_2058_2539_2561_3752_3785 =
    case input_3753_3783 of
        HorizContainerListInner horizcontainerlistinner0_3754 horizcontainerlistinner1_3755 ->
            let maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3723_3756 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3754 in
            let fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3724_3757 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3755 in
            let f0out0_3758 :: Int = addI maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3723_3756 fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3724_3757 in
            let fltAppE_1017_1195_1733_1745_1755_3729_3759 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3754 in
            let fltAppE_1018_1196_1734_1746_1756_3730_3760 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3755 in
            let f1out0_3761 :: Int = maxI fltAppE_1017_1195_1733_1745_1755_3729_3759 fltAppE_1018_1196_1734_1746_1756_3730_3760 in
            let maxH_326_852_1129_2376_2388_2398_3735_3762 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistinner0_3754 in
            let fltAppE_1000_1130_2377_2389_2399_3736_3763 :: Int = _FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ horizcontainerlistinner1_3755 in
            let f2out0_3764 :: Int = addI maxH_326_852_1129_2376_2388_2398_3735_3762 fltAppE_1000_1130_2377_2389_2399_3736_3763 in
            let tupled_output_2618_3741_3765 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistinner0_3754 curX_271_797_1060_2038_2057_2538_2560_3751_3784 curY_272_798_1061_2039_2058_2539_2561_3752_3785
                (tupled_output_2618_3741_3765_proj_0,tupled_output_2618_3741_3765_proj_1,tupled_output_2618_3741_3765_proj_2,tupled_output_2618_3741_3765_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_2618_3741_3765 in
            let fltAppE_986_1066_2033_2050_2065_2533_2551_3742_3766 :: Int = addI curY_272_798_1061_2039_2058_2539_2561_3752_3785 tupled_output_2618_3741_3765_proj_3 in
            let tupled_output_2562_3743_3767 :: (Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_3755 curX_271_797_1060_2038_2057_2538_2560_3751_3784 fltAppE_986_1066_2033_2050_2065_2533_2551_3742_3766
                (tupled_output_2562_3743_3767_proj_0,tupled_output_2562_3743_3767_proj_1,tupled_output_2562_3743_3767_proj_2) :: (Int,Int,HorizContainerList) = tupled_output_2562_3743_3767 in
            let f0out0_2545_3744_3768 :: Int = addI tupled_output_2618_3741_3765_proj_0 tupled_output_2562_3743_3767_proj_0 in
            let f1out0_2548_3745_3769 :: Int = maxI tupled_output_2618_3741_3765_proj_1 tupled_output_2562_3743_3767_proj_1 in
            let f2out0_2553_3746_3770 :: HorizContainerList = (HorizContainerListInner tupled_output_2618_3741_3765_proj_2 tupled_output_2562_3743_3767_proj_2) in
            (f0out0_3758, f1out0_3761, f2out0_3764, f0out0_2545_3744_3768, f1out0_2548_3745_3769, f2out0_2553_3746_3770)
        HorizContainerListEnd horizcontainerlistend0_3774 ->
            let f0out0_3775 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistend0_3774 in
            let f1out0_3776 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistend0_3774 in
            let f2out0_3777 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistend0_3774 in
            let tupled_output_2664_3748_3778 :: (Int,Int,ElementsList) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_3774 curX_271_797_1060_2038_2057_2538_2560_3751_3784 curY_272_798_1061_2039_2058_2539_2561_3752_3785
                (tupled_output_2664_3748_3778_proj_0,tupled_output_2664_3748_3778_proj_1,tupled_output_2664_3748_3778_proj_2) :: (Int,Int,ElementsList) = tupled_output_2664_3748_3778 in
            let f2out0_2558_3749_3779 :: HorizContainerList = (HorizContainerListEnd tupled_output_2664_3748_3778_proj_2) in
            (f0out0_3775, f1out0_3776, f2out0_3777, tupled_output_2664_3748_3778_proj_0, tupled_output_2664_3748_3778_proj_1, f2out0_2558_3749_3779)

_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Int,Int,Element,Int)
_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_3838_3865 curX_247_773_1029_1896_1927_3825_3866 curY_248_774_1030_1897_1928_3826_3867 =
    case input_3838_3865 of
        ImageCons imagecons0_3839 imagecons1_3840 imagecons2_3841 imagecons3_3842 ->
            let tupled_output_3904 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_3842 curY_248_774_1030_1897_1928_3826_3867 curX_247_773_1029_1896_1927_3825_3866
                (tupled_output_3904_proj_0,tupled_output_3904_proj_1,tupled_output_3904_proj_2) :: (Int,Int,NodeData) = tupled_output_3904 in
            let f2out0_3846 :: Element = (ImageCons imagecons0_3839 imagecons1_3840 imagecons2_3841 tupled_output_3904_proj_2) in
            (tupled_output_3904_proj_0, tupled_output_3904_proj_1, f2out0_3846, tupled_output_3904_proj_1)
        TextBoxCons textboxcons0_3848 textboxcons1_3849 textboxcons2_3850 textboxcons3_3851 ->
            let tupled_output_3941 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_3851 curY_248_774_1030_1897_1928_3826_3867 curX_247_773_1029_1896_1927_3825_3866
                (tupled_output_3941_proj_0,tupled_output_3941_proj_1,tupled_output_3941_proj_2) :: (Int,Int,NodeData) = tupled_output_3941 in
            let f2out0_3855 :: Element = (TextBoxCons textboxcons0_3848 textboxcons1_3849 textboxcons2_3850 tupled_output_3941_proj_2) in
            (tupled_output_3941_proj_0, tupled_output_3941_proj_1, f2out0_3855, tupled_output_3941_proj_1)
        VertContainer vertcontainer0_3857 vertcontainer1_3858 ->
            let tupled_output_4007 :: (Int,Int,Int,Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ vertcontainer0_3857 curX_247_773_1029_1896_1927_3825_3866 curY_248_774_1030_1897_1928_3826_3867
                (tupled_output_4007_proj_0,tupled_output_4007_proj_1,tupled_output_4007_proj_2,tupled_output_4007_proj_3,tupled_output_4007_proj_4,tupled_output_4007_proj_5) :: (Int,Int,Int,Int,Int,HorizContainerList) = tupled_output_4007 in
            let nData__252_778_1035_1882_1911_1937_3813_3862 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_3858 tupled_output_4007_proj_4 tupled_output_4007_proj_3 curY_248_774_1030_1897_1928_3826_3867 curX_247_773_1029_1896_1927_3825_3866 in
            let f2out0_3863 :: Element = (VertContainer tupled_output_4007_proj_5 nData__252_778_1035_1882_1911_1937_3813_3862) in
            (tupled_output_4007_proj_0, tupled_output_4007_proj_1, f2out0_3863, tupled_output_4007_proj_2)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,Int,Int,Int,HorizContainerList)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ input_3974_4004 curX_271_797_1060_2038_2057_2538_2560_3972_4005 curY_272_798_1061_2039_2058_2539_2561_3973_4006 =
    case input_3974_4004 of
        HorizContainerListInner horizcontainerlistinner0_3975 horizcontainerlistinner1_3976 ->
            let maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3944_3977 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3975 in
            let fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3945_3978 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3976 in
            let f0out0_3979 :: Int = addI maxH_326_852_1129_1345_1357_1367_1518_1530_1540_3944_3977 fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_3945_3978 in
            let fltAppE_1017_1195_1733_1745_1755_3950_3980 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistinner0_3975 in
            let fltAppE_1018_1196_1734_1746_1756_3951_3981 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_3976 in
            let f1out0_3982 :: Int = maxI fltAppE_1017_1195_1733_1745_1755_3950_3980 fltAppE_1018_1196_1734_1746_1756_3951_3981 in
            let fltAppE_1017_1195_2199_2211_2221_3956_3983 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistinner0_3975 in
            let fltAppE_1018_1196_2200_2212_2222_3957_3984 :: Int = _FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ horizcontainerlistinner1_3976 in
            let f2out0_3985 :: Int = maxI fltAppE_1017_1195_2199_2211_2221_3956_3983 fltAppE_1018_1196_2200_2212_2222_3957_3984 in
            let tupled_output_2618_3962_3986 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistinner0_3975 curX_271_797_1060_2038_2057_2538_2560_3972_4005 curY_272_798_1061_2039_2058_2539_2561_3973_4006
                (tupled_output_2618_3962_3986_proj_0,tupled_output_2618_3962_3986_proj_1,tupled_output_2618_3962_3986_proj_2,tupled_output_2618_3962_3986_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_2618_3962_3986 in
            let fltAppE_986_1066_2033_2050_2065_2533_2551_3963_3987 :: Int = addI curY_272_798_1061_2039_2058_2539_2561_3973_4006 tupled_output_2618_3962_3986_proj_3 in
            let tupled_output_2562_3964_3988 :: (Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_3976 curX_271_797_1060_2038_2057_2538_2560_3972_4005 fltAppE_986_1066_2033_2050_2065_2533_2551_3963_3987
                (tupled_output_2562_3964_3988_proj_0,tupled_output_2562_3964_3988_proj_1,tupled_output_2562_3964_3988_proj_2) :: (Int,Int,HorizContainerList) = tupled_output_2562_3964_3988 in
            let f0out0_2545_3965_3989 :: Int = addI tupled_output_2618_3962_3986_proj_0 tupled_output_2562_3964_3988_proj_0 in
            let f1out0_2548_3966_3990 :: Int = maxI tupled_output_2618_3962_3986_proj_1 tupled_output_2562_3964_3988_proj_1 in
            let f2out0_2553_3967_3991 :: HorizContainerList = (HorizContainerListInner tupled_output_2618_3962_3986_proj_2 tupled_output_2562_3964_3988_proj_2) in
            (f0out0_3979, f1out0_3982, f2out0_3985, f0out0_2545_3965_3989, f1out0_2548_3966_3990, f2out0_2553_3967_3991)
        HorizContainerListEnd horizcontainerlistend0_3995 ->
            let f0out0_3996 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistend0_3995 in
            let f1out0_3997 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistend0_3995 in
            let f2out0_3998 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ horizcontainerlistend0_3995 in
            let tupled_output_2664_3969_3999 :: (Int,Int,ElementsList) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_3995 curX_271_797_1060_2038_2057_2538_2560_3972_4005 curY_272_798_1061_2039_2058_2539_2561_3973_4006
                (tupled_output_2664_3969_3999_proj_0,tupled_output_2664_3969_3999_proj_1,tupled_output_2664_3969_3999_proj_2) :: (Int,Int,ElementsList) = tupled_output_2664_3969_3999 in
            let f2out0_2558_3970_4000 :: HorizContainerList = (HorizContainerListEnd tupled_output_2664_3969_3999_proj_2) in
            (f0out0_3996, f1out0_3997, f2out0_3998, tupled_output_2664_3969_3999_proj_0, tupled_output_2664_3969_3999_proj_1, f2out0_2558_3970_4000)

_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ :: Element -> Int -> Int -> (Int,Int,Element)
_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ input_4049_4073 curX_247_773_1029_1896_1927_4047_4074 curY_248_774_1030_1897_1928_4048_4075 =
    case input_4049_4073 of
        ImageCons imagecons0_4050 imagecons1_4051 imagecons2_4052 imagecons3_4053 ->
            let tupled_output_4112 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_4053 curY_248_774_1030_1897_1928_4048_4075 curX_247_773_1029_1896_1927_4047_4074
                (tupled_output_4112_proj_0,tupled_output_4112_proj_1,tupled_output_4112_proj_2) :: (Int,Int,NodeData) = tupled_output_4112 in
            let f2out0_4057 :: Element = (ImageCons imagecons0_4050 imagecons1_4051 imagecons2_4052 tupled_output_4112_proj_2) in
            (tupled_output_4112_proj_0, tupled_output_4112_proj_1, f2out0_4057)
        TextBoxCons textboxcons0_4058 textboxcons1_4059 textboxcons2_4060 textboxcons3_4061 ->
            let tupled_output_4149 :: (Int,Int,NodeData) = _TUP__t_getHeight_t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_4061 curY_248_774_1030_1897_1928_4048_4075 curX_247_773_1029_1896_1927_4047_4074
                (tupled_output_4149_proj_0,tupled_output_4149_proj_1,tupled_output_4149_proj_2) :: (Int,Int,NodeData) = tupled_output_4149 in
            let f2out0_4065 :: Element = (TextBoxCons textboxcons0_4058 textboxcons1_4059 textboxcons2_4060 tupled_output_4149_proj_2) in
            (tupled_output_4149_proj_0, tupled_output_4149_proj_1, f2out0_4065)
        VertContainer vertcontainer0_4066 vertcontainer1_4067 ->
            let tupled_output_4205 :: (Int,Int,Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ vertcontainer0_4066 curX_247_773_1029_1896_1927_4047_4074 curY_248_774_1030_1897_1928_4048_4075
                (tupled_output_4205_proj_0,tupled_output_4205_proj_1,tupled_output_4205_proj_2,tupled_output_4205_proj_3,tupled_output_4205_proj_4) :: (Int,Int,Int,Int,HorizContainerList) = tupled_output_4205 in
            let nData__252_778_1035_1882_1911_1937_4035_4071 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_4067 tupled_output_4205_proj_3 tupled_output_4205_proj_2 curY_248_774_1030_1897_1928_4048_4075 curX_247_773_1029_1896_1927_4047_4074 in
            let f2out0_4072 :: Element = (VertContainer tupled_output_4205_proj_4 nData__252_778_1035_1882_1911_1937_4035_4071) in
            (tupled_output_4205_proj_0, tupled_output_4205_proj_1, f2out0_4072)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,Int,Int,HorizContainerList)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP__TUP_ input_4176_4202 curX_271_797_1060_2038_2057_2538_2560_4174_4203 curY_272_798_1061_2039_2058_2539_2561_4175_4204 =
    case input_4176_4202 of
        HorizContainerListInner horizcontainerlistinner0_4177 horizcontainerlistinner1_4178 ->
            let maxH_326_852_1129_1345_1357_1367_1518_1530_1540_4152_4179 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistinner0_4177 in
            let fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_4153_4180 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_4178 in
            let f0out0_4181 :: Int = addI maxH_326_852_1129_1345_1357_1367_1518_1530_1540_4152_4179 fltAppE_1000_1130_1346_1358_1368_1519_1531_1541_4153_4180 in
            let fltAppE_1017_1195_1733_1745_1755_4158_4182 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistinner0_4177 in
            let fltAppE_1018_1196_1734_1746_1756_4159_4183 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ horizcontainerlistinner1_4178 in
            let f1out0_4184 :: Int = maxI fltAppE_1017_1195_1733_1745_1755_4158_4182 fltAppE_1018_1196_1734_1746_1756_4159_4183 in
            let tupled_output_2618_4164_4185 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistinner0_4177 curX_271_797_1060_2038_2057_2538_2560_4174_4203 curY_272_798_1061_2039_2058_2539_2561_4175_4204
                (tupled_output_2618_4164_4185_proj_0,tupled_output_2618_4164_4185_proj_1,tupled_output_2618_4164_4185_proj_2,tupled_output_2618_4164_4185_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_2618_4164_4185 in
            let fltAppE_986_1066_2033_2050_2065_2533_2551_4165_4186 :: Int = addI curY_272_798_1061_2039_2058_2539_2561_4175_4204 tupled_output_2618_4164_4185_proj_3 in
            let tupled_output_2562_4166_4187 :: (Int,Int,HorizContainerList) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_4178 curX_271_797_1060_2038_2057_2538_2560_4174_4203 fltAppE_986_1066_2033_2050_2065_2533_2551_4165_4186
                (tupled_output_2562_4166_4187_proj_0,tupled_output_2562_4166_4187_proj_1,tupled_output_2562_4166_4187_proj_2) :: (Int,Int,HorizContainerList) = tupled_output_2562_4166_4187 in
            let f0out0_2545_4167_4188 :: Int = addI tupled_output_2618_4164_4185_proj_0 tupled_output_2562_4166_4187_proj_0 in
            let f1out0_2548_4168_4189 :: Int = maxI tupled_output_2618_4164_4185_proj_1 tupled_output_2562_4166_4187_proj_1 in
            let f2out0_2553_4169_4190 :: HorizContainerList = (HorizContainerListInner tupled_output_2618_4164_4185_proj_2 tupled_output_2562_4166_4187_proj_2) in
            (f0out0_4181, f1out0_4184, f0out0_2545_4167_4188, f1out0_2548_4168_4189, f2out0_2553_4169_4190)
        HorizContainerListEnd horizcontainerlistend0_4194 ->
            let f0out0_4195 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ horizcontainerlistend0_4194 in
            let f1out0_4196 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ horizcontainerlistend0_4194 in
            let tupled_output_2664_4171_4197 :: (Int,Int,ElementsList) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_4194 curX_271_797_1060_2038_2057_2538_2560_4174_4203 curY_272_798_1061_2039_2058_2539_2561_4175_4204
                (tupled_output_2664_4171_4197_proj_0,tupled_output_2664_4171_4197_proj_1,tupled_output_2664_4171_4197_proj_2) :: (Int,Int,ElementsList) = tupled_output_2664_4171_4197 in
            let f2out0_2558_4172_4198 :: HorizContainerList = (HorizContainerListEnd tupled_output_2664_4171_4197_proj_2) in
            (f0out0_4195, f1out0_4196, tupled_output_2664_4171_4197_proj_0, tupled_output_2664_4171_4197_proj_1, f2out0_2558_4172_4198)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,HorizContainerList,Int,Int)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ input_4315_4341 curX_271_797_1060_2038_2057_4301_4342 curY_272_798_1061_2039_2058_4302_4343 =
    case input_4315_4341 of
        HorizContainerListInner horizcontainerlistinner0_4316 horizcontainerlistinner1_4317 ->
            let tupled_output_4416 :: (Int,Int,Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP__TUP_ horizcontainerlistinner0_4316 curX_271_797_1060_2038_2057_4301_4342 curY_272_798_1061_2039_2058_4302_4343
                (tupled_output_4416_proj_0,tupled_output_4416_proj_1,tupled_output_4416_proj_2,tupled_output_4416_proj_3,tupled_output_4416_proj_4,tupled_output_4416_proj_5) :: (Int,Int,Int,Int,ElementsList,Int) = tupled_output_4416 in
            let fltAppE_986_1066_2033_2050_2065_4296_4325 :: Int = addI curY_272_798_1061_2039_2058_4302_4343 tupled_output_4416_proj_5 in
            let tupled_output_4344 :: (Int,Int,HorizContainerList,Int,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_4317 curX_271_797_1060_2038_2057_4301_4342 fltAppE_986_1066_2033_2050_2065_4296_4325
                (tupled_output_4344_proj_0,tupled_output_4344_proj_1,tupled_output_4344_proj_2,tupled_output_4344_proj_3,tupled_output_4344_proj_4) :: (Int,Int,HorizContainerList,Int,Int) = tupled_output_4344 in
            let f0out0_4320 :: Int = addI tupled_output_4416_proj_0 tupled_output_4344_proj_0 in
            let f1out0_4323 :: Int = maxI tupled_output_4416_proj_1 tupled_output_4344_proj_1 in
            let f2out0_4327 :: HorizContainerList = (HorizContainerListInner tupled_output_4416_proj_4 tupled_output_4344_proj_2) in
            let f3out0_4330 :: Int = maxI tupled_output_4416_proj_2 tupled_output_4344_proj_3 in
            let f4out0_4333 :: Int = addI tupled_output_4416_proj_3 tupled_output_4344_proj_4 in
            (f0out0_4320, f1out0_4323, f2out0_4327, f3out0_4330, f4out0_4333)
        HorizContainerListEnd horizcontainerlistend0_4334 ->
            let tupled_output_4480 :: (Int,Int,ElementsList,Int,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_4334 curX_271_797_1060_2038_2057_4301_4342 curY_272_798_1061_2039_2058_4302_4343
                (tupled_output_4480_proj_0,tupled_output_4480_proj_1,tupled_output_4480_proj_2,tupled_output_4480_proj_3,tupled_output_4480_proj_4) :: (Int,Int,ElementsList,Int,Int) = tupled_output_4480 in
            let f2out0_4338 :: HorizContainerList = (HorizContainerListEnd tupled_output_4480_proj_2) in
            (tupled_output_4480_proj_0, tupled_output_4480_proj_1, f2out0_4338, tupled_output_4480_proj_3, tupled_output_4480_proj_4)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP__TUP_ :: ElementsList -> Int -> Int -> (Int,Int,Int,Int,ElementsList,Int)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP__TUP_ input_4382_4413 curX_262_788_1049_2086_2105_2675_2699_4380_4414 curY_263_789_1050_2087_2106_2676_2700_4381_4415 =
    case input_4382_4413 of
        ElementsListInner elementslistinner0_4383 elementslistinner1_4384 ->
            let h1_320_846_1123_1380_1392_1402_1553_1565_1575_4347_4385 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ elementslistinner1_4384 in
            let h2_321_847_1124_1381_1393_1403_1554_1566_1576_4348_4386 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ elementslistinner0_4383 in
            let f0out0_4387 :: Int = maxI h1_320_846_1123_1380_1392_1402_1553_1565_1575_4347_4385 h2_321_847_1124_1381_1393_1403_1554_1566_1576_4348_4386 in
            let fltAppE_1015_1189_1768_1780_1790_4353_4388 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ elementslistinner0_4383 in
            let fltAppE_1016_1190_1769_1781_1791_4354_4389 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ elementslistinner1_4384 in
            let f1out0_4390 :: Int = addI fltAppE_1015_1189_1768_1780_1790_4353_4388 fltAppE_1016_1190_1769_1781_1791_4354_4389 in
            let fltAppE_1015_1189_2234_2246_2256_4359_4391 :: Int = _FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistinner0_4383 in
            let fltAppE_1016_1190_2235_2247_2257_4360_4392 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elementslistinner1_4384 in
            let f2out0_4393 :: Int = addI fltAppE_1015_1189_2234_2246_2256_4359_4391 fltAppE_1016_1190_2235_2247_2257_4360_4392 in
            let h1_320_846_1123_2269_2281_2291_4365_4394 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elementslistinner1_4384 in
            let h2_321_847_1124_2270_2282_2292_4366_4395 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistinner0_4383 in
            let f3out0_4396 :: Int = maxI h1_320_846_1123_2269_2281_2291_4365_4394 h2_321_847_1124_2270_2282_2292_4366_4395 in
            let tupled_output_2771_4371_4397 :: (Element,Int,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistinner0_4383 curX_262_788_1049_2086_2105_2675_2699_4380_4414 curY_263_789_1050_2087_2106_2676_2700_4381_4415
                (tupled_output_2771_4371_4397_proj_0,tupled_output_2771_4371_4397_proj_1,tupled_output_2771_4371_4397_proj_2) :: (Element,Int,Int) = tupled_output_2771_4371_4397 in
            let fltAppE_984_1055_2081_2098_2113_2670_2688_4372_4398 :: Int = addI curX_262_788_1049_2086_2105_2675_2699_4380_4414 tupled_output_2771_4371_4397_proj_1 in
            let tupled_output_2772_4373_4399 :: (ElementsList,Int) = _TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elementslistinner1_4384 fltAppE_984_1055_2081_2098_2113_2670_2688_4372_4398 curY_263_789_1050_2087_2106_2676_2700_4381_4415
                (tupled_output_2772_4373_4399_proj_0,tupled_output_2772_4373_4399_proj_1) :: (ElementsList,Int) = tupled_output_2772_4373_4399 in
            let f0out0_2690_4374_4400 :: ElementsList = (ElementsListInner tupled_output_2771_4371_4397_proj_0 tupled_output_2772_4373_4399_proj_0) in
            let f1out0_2693_4375_4401 :: Int = maxI tupled_output_2772_4373_4399_proj_1 tupled_output_2771_4371_4397_proj_2 in
            (f0out0_4387, f1out0_4390, f2out0_4393, f3out0_4396, f0out0_2690_4374_4400, f1out0_2693_4375_4401)
        ElementsListEnd elementslistend0_4404 ->
            let f0out0_4405 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ elementslistend0_4404 in
            let f1out0_4406 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ elementslistend0_4404 in
            let f2out0_4407 :: Int = _FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistend0_4404 in
            let f3out0_4408 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistend0_4404 in
            let tupled_output_2829_4377_4409 :: (Element,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistend0_4404 curX_262_788_1049_2086_2105_2675_2699_4380_4414 curY_263_789_1050_2087_2106_2676_2700_4381_4415
                (tupled_output_2829_4377_4409_proj_0,tupled_output_2829_4377_4409_proj_1) :: (Element,Int) = tupled_output_2829_4377_4409 in
            let f0out0_2696_4378_4410 :: ElementsList = (ElementsListEnd tupled_output_2829_4377_4409_proj_0) in
            (f0out0_4405, f1out0_4406, f2out0_4407, f3out0_4408, f0out0_2696_4378_4410, tupled_output_2829_4377_4409_proj_1)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ :: ElementsList -> Int -> Int -> (Int,Int,ElementsList,Int,Int)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ input_4451_4477 curX_262_788_1049_2086_2105_4437_4478 curY_263_789_1050_2087_2106_4438_4479 =
    case input_4451_4477 of
        ElementsListInner elementslistinner0_4452 elementslistinner1_4453 ->
            let h1_320_846_1123_1380_1392_1402_1553_1565_1575_4419_4454 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ elementslistinner1_4453 in
            let h2_321_847_1124_1381_1393_1403_1554_1566_1576_4420_4455 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ elementslistinner0_4452 in
            let f0out0_4456 :: Int = maxI h1_320_846_1123_1380_1392_1402_1553_1565_1575_4419_4454 h2_321_847_1124_1381_1393_1403_1554_1566_1576_4420_4455 in
            let fltAppE_1015_1189_1768_1780_1790_4425_4457 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ elementslistinner0_4452 in
            let fltAppE_1016_1190_1769_1781_1791_4426_4458 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ elementslistinner1_4453 in
            let f1out0_4459 :: Int = addI fltAppE_1015_1189_1768_1780_1790_4425_4457 fltAppE_1016_1190_1769_1781_1791_4426_4458 in
            let tupled_output_3001_4431_4460 :: (Element,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistinner0_4452 curX_262_788_1049_2086_2105_4437_4478 curY_263_789_1050_2087_2106_4438_4479
                (tupled_output_3001_4431_4460_proj_0,tupled_output_3001_4431_4460_proj_1) :: (Element,Int) = tupled_output_3001_4431_4460 in
            let fltAppE_984_1055_2081_2098_2113_4432_4461 :: Int = addI curX_262_788_1049_2086_2105_4437_4478 tupled_output_3001_4431_4460_proj_1 in
            let remList__268_794_1056_2082_2099_2114_4433_4462 :: ElementsList = _FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elementslistinner1_4453 fltAppE_984_1055_2081_2098_2113_4432_4461 curY_263_789_1050_2087_2106_4438_4479 in
            let f2out0_4463 :: ElementsList = (ElementsListInner tupled_output_3001_4431_4460_proj_0 remList__268_794_1056_2082_2099_2114_4433_4462) in
            let fltAppE_1015_1189_2234_2246_2256_4441_4464 :: Int = _FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistinner0_4452 in
            let fltAppE_1016_1190_2235_2247_2257_4442_4465 :: Int = _FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elementslistinner1_4453 in
            let f3out0_4466 :: Int = addI fltAppE_1015_1189_2234_2246_2256_4441_4464 fltAppE_1016_1190_2235_2247_2257_4442_4465 in
            let h1_320_846_1123_2269_2281_2291_4447_4467 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elementslistinner1_4453 in
            let h2_321_847_1124_2270_2282_2292_4448_4468 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistinner0_4452 in
            let f4out0_4469 :: Int = maxI h1_320_846_1123_2269_2281_2291_4447_4467 h2_321_847_1124_2270_2282_2292_4448_4468 in
            (f0out0_4456, f1out0_4459, f2out0_4463, f3out0_4466, f4out0_4469)
        ElementsListEnd elementslistend0_4470 ->
            let f0out0_4471 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ elementslistend0_4470 in
            let f1out0_4472 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ elementslistend0_4470 in
            let fltPkd_985_1058_2084_2103_2117_4435_4473 :: Element = _FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistend0_4470 curX_262_788_1049_2086_2105_4437_4478 curY_263_789_1050_2087_2106_4438_4479 in
            let f2out0_4474 :: ElementsList = (ElementsListEnd fltPkd_985_1058_2084_2103_2117_4435_4473) in
            let f3out0_4475 :: Int = _FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistend0_4470 in
            let f4out0_4476 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistend0_4470 in
            (f0out0_4471, f1out0_4472, f2out0_4474, f3out0_4475, f4out0_4476)

_TUP__t_getHeight_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ :: NodeData -> Int -> Int -> (Int,NodeData)
_TUP__t_getHeight_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ input_4498_4507 y_377_903_1199_1957_1976_4496_4508 x_385_911_1207_1965_1977_4497_4509 =
    case input_4498_4507 of
        NodeDataK nodedatak0_4499 nodedatak1_4500 nodedatak2_4501 nodedatak3_4502 nodedatak4_4503 nodedatak5_4504 ->
            let f1out0_4506 :: NodeData = (NodeDataK x_385_911_1207_1965_1977_4497_4509 y_377_903_1199_1957_1976_4496_4508 nodedatak2_4501 nodedatak3_4502 nodedatak4_4503 nodedatak5_4504) in
            (nodedatak2_4501, f1out0_4506)

_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ :: HorizContainerList -> Int -> Int -> (Int,Int,HorizContainerList,Int)
_TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ input_4568_4590 curX_271_797_1060_2038_2057_4560_4591 curY_272_798_1061_2039_2058_4561_4592 =
    case input_4568_4590 of
        HorizContainerListInner horizcontainerlistinner0_4569 horizcontainerlistinner1_4570 ->
            let tupled_output_4655 :: (Int,Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP__TUP_ horizcontainerlistinner0_4569 curX_271_797_1060_2038_2057_4560_4591 curY_272_798_1061_2039_2058_4561_4592
                (tupled_output_4655_proj_0,tupled_output_4655_proj_1,tupled_output_4655_proj_2,tupled_output_4655_proj_3,tupled_output_4655_proj_4) :: (Int,Int,Int,ElementsList,Int) = tupled_output_4655 in
            let fltAppE_986_1066_2033_2050_2065_4555_4578 :: Int = addI curY_272_798_1061_2039_2058_4561_4592 tupled_output_4655_proj_4 in
            let tupled_output_4593 :: (Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ horizcontainerlistinner1_4570 curX_271_797_1060_2038_2057_4560_4591 fltAppE_986_1066_2033_2050_2065_4555_4578
                (tupled_output_4593_proj_0,tupled_output_4593_proj_1,tupled_output_4593_proj_2,tupled_output_4593_proj_3) :: (Int,Int,HorizContainerList,Int) = tupled_output_4593 in
            let f0out0_4573 :: Int = addI tupled_output_4655_proj_0 tupled_output_4593_proj_0 in
            let f1out0_4576 :: Int = maxI tupled_output_4655_proj_1 tupled_output_4593_proj_1 in
            let f2out0_4580 :: HorizContainerList = (HorizContainerListInner tupled_output_4655_proj_3 tupled_output_4593_proj_2) in
            let f3out0_4583 :: Int = addI tupled_output_4655_proj_2 tupled_output_4593_proj_3 in
            (f0out0_4573, f1out0_4576, f2out0_4580, f3out0_4583)
        HorizContainerListEnd horizcontainerlistend0_4584 ->
            let tupled_output_4656 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ horizcontainerlistend0_4584 curX_271_797_1060_2038_2057_4560_4591 curY_272_798_1061_2039_2058_4561_4592
                (tupled_output_4656_proj_0,tupled_output_4656_proj_1,tupled_output_4656_proj_2,tupled_output_4656_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_4656 in
            let f2out0_4588 :: HorizContainerList = (HorizContainerListEnd tupled_output_4656_proj_2) in
            (tupled_output_4656_proj_0, tupled_output_4656_proj_1, f2out0_4588, tupled_output_4656_proj_3)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP__TUP_ :: ElementsList -> Int -> Int -> (Int,Int,Int,ElementsList,Int)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP__TUP_ input_4625_4652 curX_262_788_1049_2086_2105_2675_2699_4623_4653 curY_263_789_1050_2087_2106_2676_2700_4624_4654 =
    case input_4625_4652 of
        ElementsListInner elementslistinner0_4626 elementslistinner1_4627 ->
            let h1_320_846_1123_1380_1392_1402_1553_1565_1575_4596_4628 :: Int = _FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS_ elementslistinner1_4627 in
            let h2_321_847_1124_1381_1393_1403_1554_1566_1576_4597_4629 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ elementslistinner0_4626 in
            let f0out0_4630 :: Int = maxI h1_320_846_1123_1380_1392_1402_1553_1565_1575_4596_4628 h2_321_847_1124_1381_1393_1403_1554_1566_1576_4597_4629 in
            let fltAppE_1015_1189_1768_1780_1790_4602_4631 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ elementslistinner0_4626 in
            let fltAppE_1016_1190_1769_1781_1791_4603_4632 :: Int = _FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS_ elementslistinner1_4627 in
            let f1out0_4633 :: Int = addI fltAppE_1015_1189_1768_1780_1790_4602_4631 fltAppE_1016_1190_1769_1781_1791_4603_4632 in
            let h1_320_846_1123_2269_2281_2291_4608_4634 :: Int = _FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS_ elementslistinner1_4627 in
            let h2_321_847_1124_2270_2282_2292_4609_4635 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistinner0_4626 in
            let f2out0_4636 :: Int = maxI h1_320_846_1123_2269_2281_2291_4608_4634 h2_321_847_1124_2270_2282_2292_4609_4635 in
            let tupled_output_2771_4614_4637 :: (Element,Int,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistinner0_4626 curX_262_788_1049_2086_2105_2675_2699_4623_4653 curY_263_789_1050_2087_2106_2676_2700_4624_4654
                (tupled_output_2771_4614_4637_proj_0,tupled_output_2771_4614_4637_proj_1,tupled_output_2771_4614_4637_proj_2) :: (Element,Int,Int) = tupled_output_2771_4614_4637 in
            let fltAppE_984_1055_2081_2098_2113_2670_2688_4615_4638 :: Int = addI curX_262_788_1049_2086_2105_2675_2699_4623_4653 tupled_output_2771_4614_4637_proj_1 in
            let tupled_output_2772_4616_4639 :: (ElementsList,Int) = _TUP__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_getMaxHeight_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elementslistinner1_4627 fltAppE_984_1055_2081_2098_2113_2670_2688_4615_4638 curY_263_789_1050_2087_2106_2676_2700_4624_4654
                (tupled_output_2772_4616_4639_proj_0,tupled_output_2772_4616_4639_proj_1) :: (ElementsList,Int) = tupled_output_2772_4616_4639 in
            let f0out0_2690_4617_4640 :: ElementsList = (ElementsListInner tupled_output_2771_4614_4637_proj_0 tupled_output_2772_4616_4639_proj_0) in
            let f1out0_2693_4618_4641 :: Int = maxI tupled_output_2772_4616_4639_proj_1 tupled_output_2771_4614_4637_proj_2 in
            (f0out0_4630, f1out0_4633, f2out0_4636, f0out0_2690_4617_4640, f1out0_2693_4618_4641)
        ElementsListEnd elementslistend0_4644 ->
            let f0out0_4645 :: Int = _FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS_ elementslistend0_4644 in
            let f1out0_4646 :: Int = _FUS_f_getWidthElement_f_resolveWidthElm_FUS_ elementslistend0_4644 in
            let f2out0_4647 :: Int = _FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ elementslistend0_4644 in
            let tupled_output_2829_4620_4648 :: (Element,Int) = _TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistend0_4644 curX_262_788_1049_2086_2105_2675_2699_4623_4653 curY_263_789_1050_2087_2106_2676_2700_4624_4654
                (tupled_output_2829_4620_4648_proj_0,tupled_output_2829_4620_4648_proj_1) :: (Element,Int) = tupled_output_2829_4620_4648 in
            let f0out0_2696_4621_4649 :: ElementsList = (ElementsListEnd tupled_output_2829_4620_4648_proj_0) in
            (f0out0_4645, f1out0_4646, f2out0_4647, f0out0_2696_4621_4649, tupled_output_2829_4620_4648_proj_1)

_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP__TUP_ :: Element -> Int -> Int -> (Int,Int,Int,Int,Element,Int)
_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getHeightElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP__TUP_ input_4785_4821 curX_247_773_1029_1896_1927_2848_2885_4783_4822 curY_248_774_1030_1897_1928_2849_2886_4784_4823 =
    case input_4785_4821 of
        ImageCons imagecons0_4786 imagecons1_4787 imagecons2_4788 imagecons3_4789 ->
            let f0out0_4790 :: Int = getHeight imagecons3_4789 in
            let f1out0_4791 :: Int = getWidth imagecons3_4789 in
            let tupled_output_2915_4769_4794 :: (Int,NodeData) = _TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_4789 curY_248_774_1030_1897_1928_2849_2886_4784_4823 curX_247_773_1029_1896_1927_2848_2885_4783_4822
                (tupled_output_2915_4769_4794_proj_0,tupled_output_2915_4769_4794_proj_1) :: (Int,NodeData) = tupled_output_2915_4769_4794 in
            let f0out0_2867_4770_4795 :: Element = (ImageCons imagecons0_4786 imagecons1_4787 imagecons2_4788 tupled_output_2915_4769_4794_proj_1) in
            (f0out0_4790, f1out0_4791, f1out0_4791, f0out0_4790, f0out0_2867_4770_4795, tupled_output_2915_4769_4794_proj_0)
        TextBoxCons textboxcons0_4798 textboxcons1_4799 textboxcons2_4800 textboxcons3_4801 ->
            let f0out0_4802 :: Int = getHeight textboxcons3_4801 in
            let f1out0_4803 :: Int = getWidth textboxcons3_4801 in
            let tupled_output_2944_4775_4806 :: (Int,NodeData) = _TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_4801 curY_248_774_1030_1897_1928_2849_2886_4784_4823 curX_247_773_1029_1896_1927_2848_2885_4783_4822
                (tupled_output_2944_4775_4806_proj_0,tupled_output_2944_4775_4806_proj_1) :: (Int,NodeData) = tupled_output_2944_4775_4806 in
            let f0out0_2874_4776_4807 :: Element = (TextBoxCons textboxcons0_4798 textboxcons1_4799 textboxcons2_4800 tupled_output_2944_4775_4806_proj_1) in
            (f0out0_4802, f1out0_4803, f1out0_4803, f0out0_4802, f0out0_2874_4776_4807, tupled_output_2944_4775_4806_proj_0)
        VertContainer vertcontainer0_4810 vertcontainer1_4811 ->
            let f0out0_4812 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ vertcontainer0_4810 in
            let f1out0_4813 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ vertcontainer0_4810 in
            let f2out0_4814 :: Int = _FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ vertcontainer0_4810 in
            let f3out0_4815 :: Int = _FUS_f_getSumHeights_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ vertcontainer0_4810 in
            let tupled_output_3000_4779_4816 :: (Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ vertcontainer0_4810 curX_247_773_1029_1896_1927_2848_2885_4783_4822 curY_248_774_1030_1897_1928_2849_2886_4784_4823
                (tupled_output_3000_4779_4816_proj_0,tupled_output_3000_4779_4816_proj_1,tupled_output_3000_4779_4816_proj_2,tupled_output_3000_4779_4816_proj_3) :: (Int,Int,HorizContainerList,Int) = tupled_output_3000_4779_4816 in
            let nData__252_778_1035_1882_1911_1937_2836_2881_4780_4817 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_4811 tupled_output_3000_4779_4816_proj_1 tupled_output_3000_4779_4816_proj_0 curY_248_774_1030_1897_1928_2849_2886_4784_4823 curX_247_773_1029_1896_1927_2848_2885_4783_4822 in
            let f0out0_2882_4781_4818 :: Element = (VertContainer tupled_output_3000_4779_4816_proj_2 nData__252_778_1035_1882_1911_1937_2836_2881_4780_4817) in
            (f0out0_4812, f1out0_4813, f2out0_4814, f3out0_4815, f0out0_2882_4781_4818, tupled_output_3000_4779_4816_proj_3)

_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ :: ElementsList -> Int -> Int -> (Int,Int,ElementsList,Int)
_TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ input_4951_4973 curX_262_788_1049_2086_2105_4943_4974 curY_263_789_1050_2087_2106_4944_4975 =
    case input_4951_4973 of
        ElementsListInner elementslistinner0_4952 elementslistinner1_4953 ->
            let tupled_output_5066 :: (Int,Int,Int,Element,Int) = _TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP__TUP_ elementslistinner0_4952 curX_262_788_1049_2086_2105_4943_4974 curY_263_789_1050_2087_2106_4944_4975
                (tupled_output_5066_proj_0,tupled_output_5066_proj_1,tupled_output_5066_proj_2,tupled_output_5066_proj_3,tupled_output_5066_proj_4) :: (Int,Int,Int,Element,Int) = tupled_output_5066 in
            let fltAppE_984_1055_2081_2098_2113_4938_4961 :: Int = addI curX_262_788_1049_2086_2105_4943_4974 tupled_output_5066_proj_4 in
            let tupled_output_4976 :: (Int,Int,ElementsList,Int) = _TUP__t__FUS_f__FUS_f_getMaxHeight_f_computeHeightElmList_FUS__f_resolveWidthElmList_FUS__t__FUS_f_sumWidthsElmList_f_resolveWidthElmList_FUS__t__FUS_f_setPositionsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__t__FUS_f_sumWidthsElmList_f__FUS_f_computeHeightElmList_f_resolveWidthElmList_FUS__FUS__TUP_ elementslistinner1_4953 fltAppE_984_1055_2081_2098_2113_4938_4961 curY_263_789_1050_2087_2106_4944_4975
                (tupled_output_4976_proj_0,tupled_output_4976_proj_1,tupled_output_4976_proj_2,tupled_output_4976_proj_3) :: (Int,Int,ElementsList,Int) = tupled_output_4976 in
            let f0out0_4956 :: Int = maxI tupled_output_4976_proj_0 tupled_output_5066_proj_0 in
            let f1out0_4959 :: Int = addI tupled_output_5066_proj_1 tupled_output_4976_proj_1 in
            let f2out0_4963 :: ElementsList = (ElementsListInner tupled_output_5066_proj_3 tupled_output_4976_proj_2) in
            let f3out0_4966 :: Int = addI tupled_output_5066_proj_2 tupled_output_4976_proj_3 in
            (f0out0_4956, f1out0_4959, f2out0_4963, f3out0_4966)
        ElementsListEnd elementslistend0_4967 ->
            let tupled_output_5147 :: (Int,Int,Element,Int) = _TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP_ elementslistend0_4967 curX_262_788_1049_2086_2105_4943_4974 curY_263_789_1050_2087_2106_4944_4975
                (tupled_output_5147_proj_0,tupled_output_5147_proj_1,tupled_output_5147_proj_2,tupled_output_5147_proj_3) :: (Int,Int,Element,Int) = tupled_output_5147 in
            let f2out0_4971 :: ElementsList = (ElementsListEnd tupled_output_5147_proj_2) in
            (tupled_output_5147_proj_0, tupled_output_5147_proj_1, f2out0_4971, tupled_output_5147_proj_3)

_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP__TUP_ :: Element -> Int -> Int -> (Int,Int,Int,Element,Int)
_TUP__t__FUS_f__FUS_f_getHeightElement_f_computeHeightElement_FUS__f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f_resolveWidthElm_FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__TUP__t__FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__t__FUS_f_getWidthElement_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS__TUP__TUP_ input_5030_5063 curX_247_773_1029_1896_1927_2848_2885_5028_5064 curY_248_774_1030_1897_1928_2849_2886_5029_5065 =
    case input_5030_5063 of
        ImageCons imagecons0_5031 imagecons1_5032 imagecons2_5033 imagecons3_5034 ->
            let f0out0_5035 :: Int = getHeight imagecons3_5034 in
            let f1out0_5036 :: Int = getWidth imagecons3_5034 in
            let tupled_output_2915_5014_5038 :: (Int,NodeData) = _TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ imagecons3_5034 curY_248_774_1030_1897_1928_2849_2886_5029_5065 curX_247_773_1029_1896_1927_2848_2885_5028_5064
                (tupled_output_2915_5014_5038_proj_0,tupled_output_2915_5014_5038_proj_1) :: (Int,NodeData) = tupled_output_2915_5014_5038 in
            let f0out0_2867_5015_5039 :: Element = (ImageCons imagecons0_5031 imagecons1_5032 imagecons2_5033 tupled_output_2915_5014_5038_proj_1) in
            (f0out0_5035, f1out0_5036, f1out0_5036, f0out0_2867_5015_5039, tupled_output_2915_5014_5038_proj_0)
        TextBoxCons textboxcons0_5042 textboxcons1_5043 textboxcons2_5044 textboxcons3_5045 ->
            let f0out0_5046 :: Int = getHeight textboxcons3_5045 in
            let f1out0_5047 :: Int = getWidth textboxcons3_5045 in
            let tupled_output_2944_5020_5049 :: (Int,NodeData) = _TUP__t_getWidth_t__FUS_f_updatePosX_f_updatePosY_FUS__TUP_ textboxcons3_5045 curY_248_774_1030_1897_1928_2849_2886_5029_5065 curX_247_773_1029_1896_1927_2848_2885_5028_5064
                (tupled_output_2944_5020_5049_proj_0,tupled_output_2944_5020_5049_proj_1) :: (Int,NodeData) = tupled_output_2944_5020_5049 in
            let f0out0_2874_5021_5050 :: Element = (TextBoxCons textboxcons0_5042 textboxcons1_5043 textboxcons2_5044 tupled_output_2944_5020_5049_proj_1) in
            (f0out0_5046, f1out0_5047, f1out0_5047, f0out0_2874_5021_5050, tupled_output_2944_5020_5049_proj_0)
        VertContainer vertcontainer0_5053 vertcontainer1_5054 ->
            let f0out0_5055 :: Int = _FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS_ vertcontainer0_5053 in
            let f1out0_5056 :: Int = _FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS_ vertcontainer0_5053 in
            let f2out0_5057 :: Int = _FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS_ vertcontainer0_5053 in
            let tupled_output_3000_5024_5058 :: (Int,Int,HorizContainerList,Int) = _TUP__t__FUS_f__FUS_f_getSumHeights_f_computeHeightHzList_FUS__f_resolveWidthHzLst_FUS__t__FUS_f_getMaxWidthHzList_f_resolveWidthHzLst_FUS__t__FUS_f_setPositionsHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__t__FUS_f_getMaxWidthHzList_f__FUS_f_computeHeightHzList_f_resolveWidthHzLst_FUS__FUS__TUP_ vertcontainer0_5053 curX_247_773_1029_1896_1927_2848_2885_5028_5064 curY_248_774_1030_1897_1928_2849_2886_5029_5065
                (tupled_output_3000_5024_5058_proj_0,tupled_output_3000_5024_5058_proj_1,tupled_output_3000_5024_5058_proj_2,tupled_output_3000_5024_5058_proj_3) :: (Int,Int,HorizContainerList,Int) = tupled_output_3000_5024_5058 in
            let nData__252_778_1035_1882_1911_1937_2836_2881_5025_5059 :: NodeData = _FUS_f__FUS_f_updatePosX_f_updatePosY_FUS__f__FUS_f_updateHeight_f_updateWidth_FUS__FUS_ vertcontainer1_5054 tupled_output_3000_5024_5058_proj_1 tupled_output_3000_5024_5058_proj_0 curY_248_774_1030_1897_1928_2849_2886_5029_5065 curX_247_773_1029_1896_1927_2848_2885_5028_5064 in
            let f0out0_2882_5026_5060 :: Element = (VertContainer tupled_output_3000_5024_5058_proj_2 nData__252_778_1035_1882_1911_1937_2836_2881_5025_5059) in
            (f0out0_5055, f1out0_5056, f2out0_5057, f0out0_2882_5026_5060, tupled_output_3000_5024_5058_proj_3)

gibbon_main :: Element
gibbon_main = let fltPkd_975_1019 :: StringJ = (StrEnd) in
              let fltPkd_977_1020 :: FontStyle = (FontStyleK 1 1 1) in
              let fltPkd_976_1021 :: NodeData = (NodeDataK 1 1 1 1 1 fltPkd_977_1020) in
              let fltAppE_974_1022 :: Element = (TextBoxCons 1 1 fltPkd_975_1019 fltPkd_976_1021) in
              _FUS_f_setPositionsElm_f__FUS_f_computeHeightElement_f_resolveWidthElm_FUS__FUS_ fltAppE_974_1022 10 20

main = print gibbon_main
