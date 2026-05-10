open GibbonCompat;

datatype dat_DOM = Elem of (int  * int * int * int * int * int * int * int *  dat_DOM *  dat_DOM) | Text of (int  * int * int * int * int)| Empty ;

fun internal_copy_DOM (arg_536_881_1213) = (case arg_536_881_1213 of Elem (x_537_882_1214 , x_538_883_1215, x_539_884_1216, x_540_885_1217, x_541_886_1218, x_542_887_1219, x_543_888_1220, x_544_889_1221, x_545_890_1222, x_546_891_1223) => 
  let val y_555_900_1232 = (internal_copy_DOM x_545_890_1222) in 
  let val y_556_901_1233 = (internal_copy_DOM x_546_891_1223) in (Elem (x_537_882_1214 , x_538_883_1215, x_539_884_1216, x_540_885_1217, x_541_886_1218, x_542_887_1219, x_543_888_1220, x_544_889_1221, y_555_900_1232, y_556_901_1233)) end end 
  | Text (x_557_902_1234 , x_558_903_1235, x_559_904_1236, x_560_905_1237, x_561_906_1238) => (Text (x_557_902_1234 , x_558_903_1235, x_559_904_1236, x_560_905_1237, x_561_906_1238))
  | Empty => Empty);

fun internal_print_DOM (arg_598_829_1161) = (case arg_598_829_1161 of Elem (x_599_830_1162 , x_600_831_1163, x_601_832_1164, x_602_833_1165, x_603_834_1166, x_604_835_1167, x_605_836_1168, x_606_837_1169, x_607_838_1170, x_608_839_1171) => 
  let val wildcard_619_840_1172 = (print "(Elem") in 
  let val wildcard_630_841_1173 = (print " ") in 
  let val y_609_842_1174 = (print(Int.toString(x_599_830_1162))) in 
  let val wildcard_629_843_1175 = (print " ") in 
  let val y_610_844_1176 = (print(Int.toString(x_600_831_1163))) in 
  let val wildcard_628_845_1177 = (print " ") in 
  let val y_611_846_1178 = (print(Int.toString(x_601_832_1164))) in 
  let val wildcard_627_847_1179 = (print " ") in 
  let val y_612_848_1180 = (print(Int.toString(x_602_833_1165))) in 
  let val wildcard_626_849_1181 = (print " ") in 
  let val y_613_850_1182 = (print(Int.toString(x_603_834_1166))) in 
  let val wildcard_625_851_1183 = (print " ") in 
  let val y_614_852_1184 = (print(Int.toString(x_604_835_1167))) in 
  let val wildcard_624_853_1185 = (print " ") in 
  let val y_615_854_1186 = (print(Int.toString(x_605_836_1168))) in 
  let val wildcard_623_855_1187 = (print " ") in 
  let val y_616_856_1188 = (print(Int.toString(x_606_837_1169))) in 
  let val wildcard_622_857_1189 = (print " ") in 
  let val y_617_858_1190 = (internal_print_DOM x_607_838_1170) in 
  let val wildcard_621_859_1191 = (print " ") in 
  let val y_618_860_1192 = (internal_print_DOM x_608_839_1171) in 
  let val wildcard_620_861_1193 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end 
  | Text (x_631_862_1194 , x_632_863_1195, x_633_864_1196, x_634_865_1197, x_635_866_1198) => 
  let val wildcard_641_867_1199 = (print "(Text") in 
  let val wildcard_647_868_1200 = (print " ") in 
  let val y_636_869_1201 = (print(Int.toString(x_631_862_1194))) in 
  let val wildcard_646_870_1202 = (print " ") in 
  let val y_637_871_1203 = (print(Int.toString(x_632_863_1195))) in 
  let val wildcard_645_872_1204 = (print " ") in 
  let val y_638_873_1205 = (print(Int.toString(x_633_864_1196))) in 
  let val wildcard_644_874_1206 = (print " ") in 
  let val y_639_875_1207 = (print(Int.toString(x_634_865_1197))) in 
  let val wildcard_643_876_1208 = (print " ") in 
  let val y_640_877_1209 = (print(Int.toString(x_635_866_1198))) in 
  let val wildcard_642_878_1210 = (print ")") in () end end end end end end end end end end end end
  | Empty => 
  let val wildcard_648_879_1211 = (print "(Empty") in 
  let val wildcard_649_880_1212 = (print ")") in () end end);

fun getWidth (d_404_813_1145) = (case d_404_813_1145 of Elem (wildcard__142_405_814_1146 , wildcard__143_406_815_1147, wildcard__144_407_816_1148, wildcard__145_408_817_1149, wildcard__146_409_818_1150, wildcard__147_410_819_1151, w_411_820_1152, wildcard__148_412_821_1153, wildcard__149_413_822_1154, wildcard__150_414_823_1155) => w_411_820_1152 
  | Text (wildcard__161_415_824_1156 , wildcard__162_416_825_1157, wildcard__163_417_826_1158, w_418_827_1159, wildcard__164_419_828_1160) => w_418_827_1159
  | Empty => 0);

fun sumTextWidth (d_388_797_1127) = (case d_388_797_1127 of Text (wildcard__91_389_798_1128 , wildcard__92_390_799_1129, wildcard__93_391_800_1130, w_392_801_1131, wildcard__94_393_802_1132) => w_392_801_1131 
  | Elem (wildcard__100_394_803_1133 , wildcard__101_395_804_1134, wildcard__102_396_805_1135, wildcard__103_397_806_1136, wildcard__104_398_807_1137, wildcard__105_399_808_1138, wildcard__106_400_809_1139, wildcard__107_401_810_1140, l_402_811_1141, r_403_812_1142) => 
  let val fltPrm_945_1143 = (sumTextWidth l_402_811_1141) in 
  let val fltPrm_946_1144 = (sumTextWidth r_403_812_1142) in (fltPrm_945_1143 + fltPrm_946_1144) end end
  | Empty => 0);

fun buildRenderTree (n_383_792_1111) = 
  let val fltIf_934_1112 = (n_383_792_1111 <= 0) in 
  (if fltIf_934_1112 then 
  let val w_386_795_1115 = (20 * 14) in 
  let val h_387_796_1116 = (14 + 4) in (Text (20 , 14, 16711680, w_386_795_1115, h_387_796_1116)) end end 
   else 
  let val fltPkd_935_1117 = (n_383_792_1111 mod 7) in 
  let val fltPkd_936_1118 = (n_383_792_1111 mod 4) in 
  let val fltPrm_938_1119 = (n_383_792_1111 * 3) in 
  let val fltPkd_937_1120 = (fltPrm_938_1119 mod 8) in 
  let val fltPkd_939_1121 = (n_383_792_1111 * 5) in 
  let val fltPkd_940_1122 = (n_383_792_1111 * 10) in 
  let val fltAppE_942_1123 = (n_383_792_1111 - 1) in 
  let val fltPkd_941_1124 = (buildRenderTree fltAppE_942_1123) in 
  let val fltAppE_944_1125 = (n_383_792_1111 - 1) in 
  let val fltPkd_943_1126 = (buildRenderTree fltAppE_944_1125) in (Elem (fltPkd_935_1117 , fltPkd_936_1118, fltPkd_937_1120, fltPkd_939_1121, 0, fltPkd_940_1122, 0, 0, fltPkd_941_1124, fltPkd_943_1126)) end end end end end end end end end end) end;

fun sumArea (d_367_776_1091) = (case d_367_776_1091 of Elem (wildcard__8_368_777_1092 , wildcard__9_369_778_1093, wildcard__10_370_779_1094, wildcard__11_371_780_1095, wildcard__12_372_781_1096, wildcard__13_373_782_1097, w_374_783_1098, h_375_784_1099, l_376_785_1100, r_377_786_1101) => 
  let val fltPrm_931_1102 = (w_374_783_1098 * h_375_784_1099) in 
  let val fltPrm_932_1103 = (sumArea l_376_785_1100) in 
  let val fltPrm_930_1104 = (fltPrm_931_1102 + fltPrm_932_1103) in 
  let val fltPrm_933_1105 = (sumArea r_377_786_1101) in (fltPrm_930_1104 + fltPrm_933_1105) end end end end 
  | Text (wildcard__24_378_787_1106 , wildcard__25_379_788_1107, wildcard__26_380_789_1108, w_381_790_1109, h_382_791_1110) => (w_381_790_1109 * h_382_791_1110)
  | Empty => 0);

fun countPositioned (d_350_759_1070) = (case d_350_759_1070 of Elem (wildcard__62_351_760_1071 , wildcard__63_352_761_1072, style_353_762_1073, wildcard__64_354_763_1074, wildcard__65_355_764_1075, wildcard__66_356_765_1076, wildcard__67_357_766_1077, wildcard__68_358_767_1078, l_359_768_1079, r_360_769_1080) => 
  let val fltIf_926_1081 = (style_353_762_1073 = 1) in 
  let val here_361_770_1082 = 
  (if fltIf_926_1081 then 1 
   else 0) in 
  let val fltPrm_928_1083 = (countPositioned l_359_768_1079) in 
  let val fltPrm_927_1084 = (here_361_770_1082 + fltPrm_928_1083) in 
  let val fltPrm_929_1085 = (countPositioned r_360_769_1080) in (fltPrm_927_1084 + fltPrm_929_1085) end end end end end 
  | Text (wildcard__80_362_771_1086 , wildcard__81_363_772_1087, wildcard__82_364_773_1088, wildcard__83_365_774_1089, wildcard__84_366_775_1090) => 0
  | Empty => 0);

fun internal_traverse_DOM (arg_567_741_1052) = (case arg_567_741_1052 of Elem (x_568_742_1053 , x_569_743_1054, x_570_744_1055, x_571_745_1056, x_572_746_1057, x_573_747_1058, x_574_748_1059, x_575_749_1060, x_576_750_1061, x_577_751_1062) => 
  let val y_586_752_1063 = (internal_traverse_DOM x_576_750_1061) in 
  let val y_587_753_1064 = (internal_traverse_DOM x_577_751_1062) in () end end 
  | Text (x_588_754_1065 , x_589_755_1066, x_590_756_1067, x_591_757_1068, x_592_758_1069) => ()
  | Empty => ());

fun scaleLayout (d_314_705_1006 , k_315_706_1007) = (case d_314_705_1006 of Elem (tag_316_707_1008 , cls_317_708_1009, style_318_709_1010, cost_319_710_1011, x_320_711_1012, y_321_712_1013, w_322_713_1014, h_323_714_1015, l_324_715_1016, r_325_716_1017) => 
  let val fltPkd_916_1018 = (x_320_711_1012 * k_315_706_1007) in 
  let val fltPkd_917_1019 = (y_321_712_1013 * k_315_706_1007) in 
  let val fltPkd_918_1020 = (w_322_713_1014 * k_315_706_1007) in 
  let val fltPkd_919_1021 = (h_323_714_1015 * k_315_706_1007) in 
  let val fltPkd_920_1022 = (scaleLayout(l_324_715_1016 , k_315_706_1007)) in 
  let val fltPkd_921_1023 = (scaleLayout(r_325_716_1017 , k_315_706_1007)) in (Elem (tag_316_707_1008 , cls_317_708_1009, style_318_709_1010, cost_319_710_1011, fltPkd_916_1018, fltPkd_917_1019, fltPkd_918_1020, fltPkd_919_1021, fltPkd_920_1022, fltPkd_921_1023)) end end end end end end 
  | Text (c_326_717_1024 , f_327_718_1025, col_328_719_1026, w_329_720_1027, h_330_721_1028) => 
  let val fltPkd_922_1029 = (w_329_720_1027 * k_315_706_1007) in 
  let val fltPkd_923_1030 = (h_330_721_1028 * k_315_706_1007) in (Text (c_326_717_1024 , f_327_718_1025, col_328_719_1026, fltPkd_922_1029, fltPkd_923_1030)) end end
  | Empty => Empty);

fun max (a_295_686_983 , b_296_687_984) = 
  let val fltIf_912_985 = (a_295_686_983 < b_296_687_984) in 
  (if fltIf_912_985 then b_296_687_984 
   else a_295_686_983) end;

fun maxBottom (d_297_688_986) = (case d_297_688_986 of Elem (wildcard__35_298_689_987 , wildcard__36_299_690_988, wildcard__37_300_691_989, wildcard__38_301_692_990, wildcard__39_302_693_991, y_303_694_992, wildcard__40_304_695_993, h_305_696_994, l_306_697_995, r_307_698_996) => 
  let val here_308_699_997 = (y_303_694_992 + h_305_696_994) in 
  let val fltAppE_914_998 = (maxBottom l_306_697_995) in 
  let val fltAppE_915_999 = (maxBottom r_307_698_996) in 
  let val fltAppE_913_1000 = (max(fltAppE_914_998 , fltAppE_915_999)) in (max(here_308_699_997 , fltAppE_913_1000)) end end end end 
  | Text (wildcard__52_309_700_1001 , wildcard__53_310_701_1002, wildcard__54_311_702_1003, wildcard__55_312_703_1004, h_313_704_1005) => h_313_704_1005
  | Empty => 0);

fun computeWidths (d_331_722_1031) = (case d_331_722_1031 of Elem (tag_332_723_1032 , cls_333_724_1033, style_334_725_1034, cost_335_726_1035, x_336_727_1036, y_337_728_1037, wildcard__119_338_729_1038, h_339_730_1039, l_340_731_1040, r_341_732_1041) => 
  let val l__342_733_1042 = (computeWidths l_340_731_1040) in 
  let val r__343_734_1043 = (computeWidths r_341_732_1041) in 
  let val fltAppE_924_1044 = (getWidth l__342_733_1042) in 
  let val fltAppE_925_1045 = (getWidth r__343_734_1043) in 
  let val w_344_735_1046 = (max(fltAppE_924_1044 , fltAppE_925_1045)) in (Elem (tag_332_723_1032 , cls_333_724_1033, style_334_725_1034, cost_335_726_1035, x_336_727_1036, y_337_728_1037, w_344_735_1046, h_339_730_1039, l__342_733_1042, r__343_734_1043)) end end end end end 
  | Text (c_345_736_1047 , f_346_737_1048, col_347_738_1049, w_348_739_1050, h_349_740_1051) => (Text (c_345_736_1047 , f_346_737_1048, col_347_738_1049, w_348_739_1050, h_349_740_1051))
  | Empty => Empty);
val _ = (case 
  let val wildcard__256_259_650_947 = (printsym "Running program DomTree: ") in 
  let val wildcard__254_260_651_948 = (printsym "NEWLINE") in 
let val tree_261_652_949 = (buildRenderTree ((GibbonCompat.getSizeParam()) + 23)) in
let val tree_smaller_262_653_950 = (buildRenderTree ((GibbonCompat.getSizeParam()) + 20)) in
  let val wildcard__250_263_654_951 = (printsym "Running pass SumArea (fold, uses=6): ") in 
  let val wildcard__248_264_655_952 = (printsym "NEWLINE") in 
  let val area_265_656_953 = (iterate (fn () => sumArea tree_261_652_949)) in 
  let val wildcard__244_266_657_954 = (printsym "End") in 
  let val wildcard__242_267_658_955 = (printsym "NEWLINE") in 
  let val wildcard__240_268_659_956 = (printsym "Running pass find max Bottom (fold, uses=5): ") in 
  let val wildcard__238_269_660_957 = (printsym "NEWLINE") in 
  let val bottom_270_661_958 = (iterate (fn () => maxBottom tree_261_652_949)) in 
  let val wildcard__234_271_662_959 = (printsym "End") in 
  let val wildcard__232_272_663_960 = (printsym "NEWLINE") in 
  let val wildcard__230_273_664_961 = (printsym "Running pass count styled (fold, uses=3): ") in 
  let val wildcard__228_274_665_962 = (printsym "NEWLINE") in 
  let val styled_275_666_963 = (iterate (fn () => countPositioned tree_261_652_949)) in 
  let val wildcard__224_276_667_964 = (printsym "End") in 
  let val wildcard__222_277_668_965 = (printsym "NEWLINE") in 
  let val wildcard__220_278_669_966 = (printsym "Running pass sumTextWidth (fold, uses=3): ") in 
  let val wildcard__218_279_670_967 = (printsym "NEWLINE") in 
  let val textW_280_671_968 = (iterate (fn () => sumTextWidth tree_261_652_949)) in 
  let val wildcard__214_281_672_969 = (printsym "End") in 
  let val wildcard__212_282_673_970 = (printsym "NEWLINE") in 
  let val wildcard__210_283_674_971 = (printsym "Running pass computeWidths (map, uses=14): ") in 
  let val wildcard__208_284_675_972 = (printsym "NEWLINE") in 
  let val tree__285_676_973 = (iterate (fn () => computeWidths tree_smaller_262_653_950)) in 
  let val wildcard__204_286_677_974 = (printsym "End") in 
  let val wildcard__202_287_678_975 = (printsym "NEWLINE") in 
  let val wildcard__200_288_679_976 = (printsym "Running pass scaleLayout (map, uses=15): ") in 
  let val wildcard__198_289_680_977 = (printsym "NEWLINE") in 
  let val tree___290_681_978 = (iterate (fn () => scaleLayout(tree__285_676_973 , 2))) in 
  let val wildcard__194_291_682_979 = (printsym "End") in 
  let val wildcard__192_292_683_980 = (printsym "NEWLINE") in 
  let val scaledArea__293_684_981 = (sumArea tree__285_676_973) in 
  let val scaledArea___294_685_982 = (sumArea tree___290_681_978) in (area_265_656_953 , bottom_270_661_958, styled_275_666_963, textW_280_671_968, scaledArea__293_684_981, scaledArea___294_685_982) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print ")" in () end);
val _ = print "\n"
