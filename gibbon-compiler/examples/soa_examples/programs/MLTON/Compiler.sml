open GibbonCompat;

datatype dat_IR = Instr of (int  * int * int * int * int * int * int *  dat_IR) | BlockEnd of ( dat_IR)| End ;

fun internal_print_IR (arg_684_934_1270) = (case arg_684_934_1270 of Instr (x_685_935_1271 , x_686_936_1272, x_687_937_1273, x_688_938_1274, x_689_939_1275, x_690_940_1276, x_691_941_1277, x_692_942_1278) => 
  let val wildcard_701_943_1279 = (print "(Instr") in 
  let val wildcard_710_944_1280 = (print " ") in 
  let val y_693_945_1281 = (print(Int.toString(x_685_935_1271))) in 
  let val wildcard_709_946_1282 = (print " ") in 
  let val y_694_947_1283 = (print(Int.toString(x_686_936_1272))) in 
  let val wildcard_708_948_1284 = (print " ") in 
  let val y_695_949_1285 = (print(Int.toString(x_687_937_1273))) in 
  let val wildcard_707_950_1286 = (print " ") in 
  let val y_696_951_1287 = (print(Int.toString(x_688_938_1274))) in 
  let val wildcard_706_952_1288 = (print " ") in 
  let val y_697_953_1289 = (print(Int.toString(x_689_939_1275))) in 
  let val wildcard_705_954_1290 = (print " ") in 
  let val y_698_955_1291 = (print(Int.toString(x_690_940_1276))) in 
  let val wildcard_704_956_1292 = (print " ") in 
  let val y_699_957_1293 = (print(Int.toString(x_691_941_1277))) in 
  let val wildcard_703_958_1294 = (print " ") in 
  let val y_700_959_1295 = (internal_print_IR x_692_942_1278) in 
  let val wildcard_702_960_1296 = (print ")") in () end end end end end end end end end end end end end end end end end end 
  | BlockEnd (x_711_961_1297) => 
  let val wildcard_713_962_1298 = (print "(BlockEnd") in 
  let val wildcard_715_963_1299 = (print " ") in 
  let val y_712_964_1300 = (internal_print_IR x_711_961_1297) in 
  let val wildcard_714_965_1301 = (print ")") in () end end end end
  | End => 
  let val wildcard_716_966_1302 = (print "(End") in 
  let val wildcard_717_967_1303 = (print ")") in () end end);

fun internal_traverse_IR (arg_665_922_1258) = (case arg_665_922_1258 of Instr (x_666_923_1259 , x_667_924_1260, x_668_925_1261, x_669_926_1262, x_670_927_1263, x_671_928_1264, x_672_929_1265, x_673_930_1266) => 
  let val y_681_931_1267 = (internal_traverse_IR x_673_930_1266) in () end 
  | BlockEnd (x_682_932_1268) => 
  let val y_683_933_1269 = (internal_traverse_IR x_682_932_1268) in () end
  | End => ());

fun internal_copy_IR (arg_646_903_1239) = (case arg_646_903_1239 of Instr (x_647_904_1240 , x_648_905_1241, x_649_906_1242, x_650_907_1243, x_651_908_1244, x_652_909_1245, x_653_910_1246, x_654_911_1247) => 
  let val y_662_919_1255 = (internal_copy_IR x_654_911_1247) in (Instr (x_647_904_1240 , x_648_905_1241, x_649_906_1242, x_650_907_1243, x_651_908_1244, x_652_909_1245, x_653_910_1246, y_662_919_1255)) end 
  | BlockEnd (x_663_920_1256) => 
  let val y_664_921_1257 = (internal_copy_IR x_663_920_1256) in (BlockEnd (y_664_921_1257)) end
  | End => End);

fun blockCountPass (ir_480_893_1228) = (case ir_480_893_1228 of BlockEnd (rest_481_894_1229) => 
  let val fltPrm_1010_1230 = (blockCountPass rest_481_894_1229) in (1 + fltPrm_1010_1230) end 
  | Instr (wildcard__30_482_895_1231 , wildcard__31_483_896_1232, wildcard__32_484_897_1233, wildcard__33_485_898_1234, wildcard__34_486_899_1235, wildcard__35_487_900_1236, wildcard__36_488_901_1237, rest_489_902_1238) => (blockCountPass rest_489_902_1238)
  | End => 0);

fun stripSideEffectsPass (ir_470_883_1216) = (case ir_470_883_1216 of Instr (op_471_884_1217 , wildcard__161_472_885_1218, s1_473_886_1219, s2_474_887_1220, dst_475_888_1221, lat_476_889_1222, thr_477_890_1223, rest_478_891_1224) => 
  let val fltPkd_1008_1225 = (stripSideEffectsPass rest_478_891_1224) in (Instr (op_471_884_1217 , 0, s1_473_886_1219, s2_474_887_1220, dst_475_888_1221, lat_476_889_1222, thr_477_890_1223, fltPkd_1008_1225)) end 
  | BlockEnd (rest_479_892_1226) => 
  let val fltPkd_1009_1227 = (stripSideEffectsPass rest_479_892_1226) in (BlockEnd (fltPkd_1009_1227)) end
  | End => End);

fun throughputModelPass (ir_460_873_1205) = (case ir_460_873_1205 of Instr (wildcard__131_461_874_1206 , wildcard__132_462_875_1207, wildcard__133_463_876_1208, wildcard__134_464_877_1209, wildcard__135_465_878_1210, wildcard__136_466_879_1211, thr_467_880_1212, rest_468_881_1213) => 
  let val fltPrm_1007_1214 = (throughputModelPass rest_468_881_1213) in (thr_467_880_1212 + fltPrm_1007_1214) end 
  | BlockEnd (rest_469_882_1215) => (throughputModelPass rest_469_882_1215)
  | End => 0);

fun memoryOpStatsPass (ir_449_862_1190) = (case ir_449_862_1190 of Instr (wildcard__81_450_863_1191 , flags_451_864_1192, wildcard__82_452_865_1193, wildcard__83_453_866_1194, wildcard__84_454_867_1195, wildcard__85_455_868_1196, wildcard__86_456_869_1197, rest_457_870_1198) => 
  let val fltPrm_1004_1199 = (flags_451_864_1192 = 1) in 
  let val fltPrm_1005_1200 = (flags_451_864_1192 = 2) in 
  let val fltIf_1003_1201 = (fltPrm_1004_1199 orelse fltPrm_1005_1200) in 
  let val isMem_458_871_1202 = 
  (if fltIf_1003_1201 then 1 
   else 0) in 
  let val fltPrm_1006_1203 = (memoryOpStatsPass rest_457_870_1198) in (isMem_458_871_1202 + fltPrm_1006_1203) end end end end end 
  | BlockEnd (rest_459_872_1204) => (memoryOpStatsPass rest_459_872_1204)
  | End => 0);

fun verifyPhiPlacement_IO (ir_436_849_1174 , seenNonPhi_437_850_1175) = (case ir_436_849_1174 of End => () 
  | BlockEnd (rest_438_851_1176) => (verifyPhiPlacement_IO(rest_438_851_1176 , 0))
  | Instr (op_439_852_1177 , fl_440_853_1178, s1_441_854_1179, s2_442_855_1180, dst_443_856_1181, lat_444_857_1182, thr_445_858_1183, rest_446_859_1184) => 
  let val fltIf_1000_1185 = (op_439_852_1177 = 6) in 
  let val wildcard__178_447_860_1187 = 
  (if fltIf_1000_1185 then 
  let val fltIf_1001_1186 = (seenNonPhi_437_850_1175 = 1) in 
  (if fltIf_1001_1186 then (print "BADPHI ") 
   else ()) end 
   else ()) in 
  let val fltIf_1002_1188 = (op_439_852_1177 = 6) in 
  let val seenNonPhi__448_861_1189 = 
  (if fltIf_1002_1188 then seenNonPhi_437_850_1175 
   else 1) in (verifyPhiPlacement_IO(rest_446_859_1184 , seenNonPhi__448_861_1189)) end end end end);

fun targetRetunePass (ir_425_838_1160 , k_426_839_1161) = (case ir_425_838_1160 of Instr (op_427_840_1162 , fl_428_841_1163, s1_429_842_1164, s2_430_843_1165, dst_431_844_1166, lat_432_845_1167, thr_433_846_1168, rest_434_847_1169) => 
  let val fltPkd_997_1170 = (lat_432_845_1167 * k_426_839_1161) in 
  let val fltPkd_998_1171 = (targetRetunePass(rest_434_847_1169 , k_426_839_1161)) in (Instr (op_427_840_1162 , fl_428_841_1163, s1_429_842_1164, s2_430_843_1165, dst_431_844_1166, fltPkd_997_1170, thr_433_846_1168, fltPkd_998_1171)) end end 
  | BlockEnd (rest_435_848_1172) => 
  let val fltPkd_999_1173 = (targetRetunePass(rest_435_848_1172 , k_426_839_1161)) in (BlockEnd (fltPkd_999_1173)) end
  | End => End);

fun branchStatsPass (ir_414_827_1147) = (case ir_414_827_1147 of Instr (wildcard__98_415_828_1148 , flags_416_829_1149, wildcard__99_417_830_1150, wildcard__100_418_831_1151, wildcard__101_419_832_1152, wildcard__102_420_833_1153, wildcard__103_421_834_1154, rest_422_835_1155) => 
  let val fltIf_995_1156 = (flags_416_829_1149 = 4) in 
  let val isBr_423_836_1157 = 
  (if fltIf_995_1156 then 1 
   else 0) in 
  let val fltPrm_996_1158 = (branchStatsPass rest_422_835_1155) in (isBr_423_836_1157 + fltPrm_996_1158) end end end 
  | BlockEnd (rest_424_837_1159) => (branchStatsPass rest_424_837_1159)
  | End => 0);

fun latencyModelPass (ir_404_817_1136) = (case ir_404_817_1136 of Instr (wildcard__115_405_818_1137 , wildcard__116_406_819_1138, wildcard__117_407_820_1139, wildcard__118_408_821_1140, wildcard__119_409_822_1141, lat_410_823_1142, wildcard__120_411_824_1143, rest_412_825_1144) => 
  let val fltPrm_994_1145 = (latencyModelPass rest_412_825_1144) in (lat_410_823_1142 + fltPrm_994_1145) end 
  | BlockEnd (rest_413_826_1146) => (latencyModelPass rest_413_826_1146)
  | End => 0);

fun goHasCycle (ir_391_804_1120 , curBlock_392_805_1121) = (case ir_391_804_1120 of Instr (op_393_806_1122 , wildcard__64_394_807_1123, tgt_395_808_1124, wildcard__65_396_809_1125, wildcard__66_397_810_1126, wildcard__67_398_811_1127, wildcard__68_399_812_1128, rest_400_813_1129) => 
  let val fltPrm_991_1130 = (op_393_806_1122 = 4) in 
  let val fltPrm_992_1131 = (tgt_395_808_1124 < curBlock_392_805_1121) in 
  let val isBackedge_401_814_1132 = (fltPrm_991_1130 andalso fltPrm_992_1131) in 
  let val restHasCycle_402_815_1133 = (goHasCycle(rest_400_813_1129 , curBlock_392_805_1121)) in (isBackedge_401_814_1132 orelse restHasCycle_402_815_1133) end end end end 
  | BlockEnd (rest_403_816_1134) => 
  let val fltAppE_993_1135 = (curBlock_392_805_1121 + 1) in (goHasCycle(rest_403_816_1134 , fltAppE_993_1135)) end
  | End => false);

fun castInstCountPass (ir_380_793_1107) = (case ir_380_793_1107 of Instr (op_381_794_1108 , wildcard__46_382_795_1109, wildcard__47_383_796_1110, wildcard__48_384_797_1111, wildcard__49_385_798_1112, wildcard__50_386_799_1113, wildcard__51_387_800_1114, rest_388_801_1115) => 
  let val fltIf_989_1116 = (op_381_794_1108 = 7) in 
  let val isCast_389_802_1117 = 
  (if fltIf_989_1116 then 1 
   else 0) in 
  let val fltPrm_990_1118 = (castInstCountPass rest_388_801_1115) in (isCast_389_802_1117 + fltPrm_990_1118) end end end 
  | BlockEnd (rest_390_803_1119) => (castInstCountPass rest_390_803_1119)
  | End => 0);

fun buildIR_validPhi_go (n_373_786_1084 , pendingPhi_374_787_1085) = 
  let val fltIf_973_1086 = (n_373_786_1084 <= 0) in 
  (if fltIf_973_1086 then End 
   else 
  let val fltIf_974_1087 = (pendingPhi_374_787_1085 > 0) in 
  (if fltIf_974_1087 then 
  let val fltAppE_976_1088 = (pendingPhi_374_787_1085 - 1) in 
  let val fltPkd_975_1089 = (buildIR_validPhi_go(n_373_786_1084 , fltAppE_976_1088)) in (Instr (6 , 0, 0, 0, 0, 1, 1, fltPkd_975_1089)) end end 
   else 
  let val fltPrm_978_1090 = (n_373_786_1084 mod 7) in 
  let val fltIf_977_1091 = (fltPrm_978_1090 = 0) in 
  (if fltIf_977_1091 then 
  let val fltAppE_980_1092 = (n_373_786_1084 - 1) in 
  let val fltPkd_979_1093 = (buildIR_validPhi_go(fltAppE_980_1092 , 2)) in (BlockEnd (fltPkd_979_1093)) end end 
   else 
  let val op0_375_788_1094 = (n_373_786_1084 mod 8) in 
  let val fltIf_981_1095 = (op0_375_788_1094 = 6) in 
  let val op_376_789_1096 = 
  (if fltIf_981_1095 then 0 
   else op0_375_788_1094) in 
  let val fltPrm_982_1097 = (n_373_786_1084 * 3) in 
  let val flags_377_790_1098 = (fltPrm_982_1097 mod 16) in 
  let val fltPrm_983_1099 = (n_373_786_1084 mod 5) in 
  let val lat_378_791_1100 = (1 + fltPrm_983_1099) in 
  let val fltPrm_984_1101 = (n_373_786_1084 mod 3) in 
  let val thr_379_792_1102 = (1 + fltPrm_984_1101) in 
  let val fltPkd_985_1103 = (n_373_786_1084 - 1) in 
  let val fltPkd_986_1104 = (n_373_786_1084 - 2) in 
  let val fltAppE_988_1105 = (n_373_786_1084 - 1) in 
  let val fltPkd_987_1106 = (buildIR_validPhi_go(fltAppE_988_1105 , 0)) in (Instr (op_376_789_1096 , flags_377_790_1098, fltPkd_985_1103, fltPkd_986_1104, n_373_786_1084, lat_378_791_1100, thr_379_792_1102, fltPkd_987_1106)) end end end end end end end end end end end end end) end end) end) end;

fun instCountPass (ir_363_776_1073) = (case ir_363_776_1073 of Instr (wildcard__12_364_777_1074 , wildcard__13_365_778_1075, wildcard__14_366_779_1076, wildcard__15_367_780_1077, wildcard__16_368_781_1078, wildcard__17_369_782_1079, wildcard__18_370_783_1080, rest_371_784_1081) => 
  let val fltPrm_972_1082 = (instCountPass rest_371_784_1081) in (1 + fltPrm_972_1082) end 
  | BlockEnd (rest_372_785_1083) => (instCountPass rest_372_785_1083)
  | End => 0);
val _ = (case 
  let val wildcard__302_305_718_1011 = (print "Running the Compiler IR Program: ") in 
  let val wildcard__300_306_719_1012 = (printsym "NEWLINE") in 
  let val fltPrm_969_1013 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_968_1014 = (fltPrm_969_1013 + 5000000) in 
  let val ir_307_720_1015 = (buildIR_validPhi_go(fltAppE_968_1014 , 0)) in 
  let val wildcard__297_308_721_1016 = (printsym "Running pass verifyIR (fold, uses=9): ") in 
  let val wildcard__295_309_722_1017 = (printsym "NEWLINE") in 
  let val wildcard__293_310_723_1018 = (verifyPhiPlacement_IO(ir_307_720_1015 , 0)) in 
  let val wildcard__290_311_724_1019 = (printsym "End") in 
  let val wildcard__288_312_725_1020 = (printsym "NEWLINE") in 
  let val wildcard__286_313_726_1021 = (printsym "Running pass instCountPass (fold, uses=2): ") in 
  let val wildcard__284_314_727_1022 = (printsym "NEWLINE") in 
  let val insts_315_728_1023 = (iterate (fn () => instCountPass ir_307_720_1015)) in 
  let val wildcard__280_316_729_1024 = (printsym "End") in 
  let val wildcard__278_317_730_1025 = (printsym "NEWLINE") in 
  let val wildcard__276_318_731_1026 = (printsym "Running pass blockCountPass (fold, uses=2): ") in 
  let val wildcard__274_319_732_1027 = (printsym "NEWLINE") in 
  let val blocks_320_733_1028 = (iterate (fn () => blockCountPass ir_307_720_1015)) in 
  let val wildcard__270_321_734_1029 = (printsym "End") in 
  let val wildcard__268_322_735_1030 = (printsym "NEWLINE") in 
  let val wildcard__266_323_736_1031 = (printsym "Running pass memoryOpStatsPass (fold, uses=3): ") in 
  let val wildcard__264_324_737_1032 = (printsym "NEWLINE") in 
  let val memops_325_738_1033 = (iterate (fn () => memoryOpStatsPass ir_307_720_1015)) in 
  let val wildcard__260_326_739_1034 = (printsym "End") in 
  let val wildcard__258_327_740_1035 = (printsym "NEWLINE") in 
  let val wildcard__256_328_741_1036 = (printsym "Running pass castInstCountPass (fold, uses=3): ") in 
  let val wildcard__254_329_742_1037 = (printsym "NEWLINE") in 
  let val castInstrs_330_743_1038 = (iterate (fn () => castInstCountPass ir_307_720_1015)) in 
  let val wildcard__250_331_744_1039 = (printsym "End") in 
  let val wildcard__248_332_745_1040 = (printsym "NEWLINE") in 
  let val wildcard__246_333_746_1041 = (printsym "Running pass branchStatsPass (fold, uses=2): ") in 
  let val wildcard__244_334_747_1042 = (printsym "NEWLINE") in 
  let val brs_335_748_1043 = (iterate (fn () => branchStatsPass ir_307_720_1015)) in 
  let val wildcard__240_336_749_1044 = (printsym "End") in 
  let val wildcard__238_337_750_1045 = (printsym "NEWLINE") in 
  let val wildcard__236_338_751_1046 = (printsym "Running pass latencyModelPass (fold, uses=3): ") in 
  let val wildcard__234_339_752_1047 = (printsym "NEWLINE") in 
  let val lat_340_753_1048 = (iterate (fn () => latencyModelPass ir_307_720_1015)) in 
  let val wildcard__230_341_754_1049 = (printsym "End") in 
  let val wildcard__228_342_755_1050 = (printsym "NEWLINE") in 
  let val wildcard__226_343_756_1051 = (printsym "Running pass has cycle (fold, uses=4): ") in 
  let val wildcard__224_344_757_1052 = (printsym "NEWLINE") in 
  let val hasCycle_345_758_1053 = (iterate (fn () => goHasCycle(ir_307_720_1015 , 0))) in 
  let val wildcard__220_346_759_1054 = (printsym "End") in 
  let val wildcard__218_347_760_1055 = (printsym "NEWLINE") in 
  let val wildcard__216_348_761_1056 = (printsym "Running pass throughputModelPass (fold, uses=3): ") in 
  let val wildcard__214_349_762_1057 = (printsym "NEWLINE") in 
  let val thr_350_763_1058 = (iterate (fn () => throughputModelPass ir_307_720_1015)) in 
  let val wildcard__210_351_764_1059 = (print "End: ") in 
  let val wildcard__208_352_765_1060 = (printsym "NEWLINE") in 
  let val wildcard__206_353_766_1061 = (printsym "Running pass targetReturnPass (map, uses=9): ") in 
  let val wildcard__204_354_767_1062 = (printsym "NEWLINE") in 
  let val ir__355_768_1063 = (iterate (fn () => targetRetunePass(ir_307_720_1015 , 2))) in 
  let val wildcard__200_356_769_1064 = (printsym "End") in 
  let val wildcard__198_357_770_1065 = (printsym "NEWLINE") in 
  let val wildcard__196_358_771_1066 = (printsym "Running pass stripSideEffectsPass (map, uses=7): ") in 
  let val wildcard__194_359_772_1067 = (printsym "NEWLINE") in 
  let val ir___360_773_1068 = (iterate (fn () => stripSideEffectsPass ir__355_768_1063)) in 
  let val wildcard__190_361_774_1069 = (printsym "End") in 
  let val wildcard__188_362_775_1070 = (printsym "NEWLINE") in 
  let val fltPrd_970_1071 = (instCountPass ir__355_768_1063) in 
  let val fltPrd_971_1072 = (instCountPass ir___360_773_1068) in (insts_315_728_1023 , blocks_320_733_1028, memops_325_738_1033, brs_335_748_1043, lat_340_753_1048, hasCycle_345_758_1053, thr_350_763_1058, fltPrd_970_1071, fltPrd_971_1072) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7, x__8, x__9) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = ((fn true => print "True" | false => print "False") x__6) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print " "val _ = (print(Int.toString(x__8))) val _ = print " "val _ = (print(Int.toString(x__9))) val _ = print ")" in () end);
val _ = print "\n"
