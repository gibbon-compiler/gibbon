open GibbonCompat;

datatype dat_PW = Leaf of (int  * int * int) | Node of (int  * int * int *  dat_PW *  dat_PW) ;

fun norm2Estimate (p_337_769_1070) = (case p_337_769_1070 of Leaf (c_338_770_1071 , s_339_771_1072, d_340_772_1073) => 
  let val fltPrm_829_1074 = (c_338_770_1071 * c_338_770_1071) in 
  let val fltPrm_831_1075 = (d_340_772_1073 * d_340_772_1073) in 
  let val fltPrm_832_1076 = (s_339_771_1072 + 1) in 
  let val fltPrm_830_1077 = (fltPrm_831_1075 div fltPrm_832_1076) in (fltPrm_829_1074 + fltPrm_830_1077) end end end end 
  | Node (wildcard__21_341_773_1078 , wildcard__22_342_774_1079, wildcard__23_343_775_1080, l_344_776_1081, r_345_777_1082) => 
  let val fltPrm_833_1083 = (norm2Estimate l_344_776_1081) in 
  let val fltPrm_834_1084 = (norm2Estimate r_345_777_1082) in (fltPrm_833_1083 + fltPrm_834_1084) end end);

fun internal_copy_PW (arg_522_752_1053) = (case arg_522_752_1053 of Leaf (x_523_753_1054 , x_524_754_1055, x_525_755_1056) => (Leaf (x_523_753_1054 , x_524_754_1055, x_525_755_1056)) 
  | Node (x_529_759_1060 , x_530_760_1061, x_531_761_1062, x_532_762_1063, x_533_763_1064) => 
  let val y_537_767_1068 = (internal_copy_PW x_532_762_1063) in 
  let val y_538_768_1069 = (internal_copy_PW x_533_763_1064) in (Node (x_529_759_1060 , x_530_760_1061, x_531_761_1062, y_537_767_1068, y_538_768_1069)) end end);

fun pmapCutHistogram (p_326_741_1038 , cut_327_742_1039) = (case p_326_741_1038 of Node (dim_328_743_1040 , split_329_744_1041, wildcard__73_330_745_1042, l_331_746_1043, r_332_747_1044) => 
  let val fltIf_825_1045 = (split_329_744_1041 > cut_327_742_1039) in 
  let val here_333_748_1046 = 
  (if fltIf_825_1045 then (dim_328_743_1040 + 1) 
   else 0) in 
  let val fltPrm_827_1047 = (pmapCutHistogram(l_331_746_1043 , cut_327_742_1039)) in 
  let val fltPrm_826_1048 = (here_333_748_1046 + fltPrm_827_1047) in 
  let val fltPrm_828_1049 = (pmapCutHistogram(r_332_747_1044 , cut_327_742_1039)) in (fltPrm_826_1048 + fltPrm_828_1049) end end end end end 
  | Leaf (wildcard__80_334_749_1050 , wildcard__81_335_750_1051, wildcard__82_336_751_1052) => 0);

fun absI (x_325_740_1036) = 
  let val fltIf_824_1037 = (x_325_740_1036 < 0) in 
  (if fltIf_824_1037 then (0 - x_325_740_1036) 
   else x_325_740_1036) end;

fun mixSeed (s_323_738_1031 , salt_324_739_1032) = 
  let val fltPrm_822_1033 = (s_323_738_1031 * 1103) in 
  let val fltPrm_823_1034 = (salt_324_739_1032 * 97) in 
  let val fltPrm_821_1035 = (fltPrm_822_1033 + fltPrm_823_1034) in (fltPrm_821_1035 + 13) end end end;

fun internal_print_PW (arg_556_700_990) = (case arg_556_700_990 of Leaf (x_557_701_991 , x_558_702_992, x_559_703_993) => 
  let val wildcard_563_704_994 = (print "(Leaf") in 
  let val wildcard_567_705_995 = (print " ") in 
  let val y_560_706_996 = (print(Int.toString(x_557_701_991))) in 
  let val wildcard_566_707_997 = (print " ") in 
  let val y_561_708_998 = (print(Int.toString(x_558_702_992))) in 
  let val wildcard_565_709_999 = (print " ") in 
  let val y_562_710_1000 = (print(Int.toString(x_559_703_993))) in 
  let val wildcard_564_711_1001 = (print ")") in () end end end end end end end end 
  | Node (x_568_712_1002 , x_569_713_1003, x_570_714_1004, x_571_715_1005, x_572_716_1006) => 
  let val wildcard_578_717_1007 = (print "(Node") in 
  let val wildcard_584_718_1008 = (print " ") in 
  let val y_573_719_1009 = (print(Int.toString(x_568_712_1002))) in 
  let val wildcard_583_720_1010 = (print " ") in 
  let val y_574_721_1011 = (print(Int.toString(x_569_713_1003))) in 
  let val wildcard_582_722_1012 = (print " ") in 
  let val y_575_723_1013 = (print(Int.toString(x_570_714_1004))) in 
  let val wildcard_581_724_1014 = (print " ") in 
  let val y_576_725_1015 = (internal_print_PW x_571_715_1005) in 
  let val wildcard_580_726_1016 = (print " ") in 
  let val y_577_727_1017 = (internal_print_PW x_572_716_1006) in 
  let val wildcard_579_728_1018 = (print ")") in () end end end end end end end end end end end end);

fun lbDeuxLoadProxy (p_305_691_974) = (case p_305_691_974 of Leaf (wildcard__87_306_692_975 , lvl_307_693_976, detail_308_694_977) => 
  let val fltPrm_811_978 = (lvl_307_693_976 + 1) in 
  let val fltPrm_813_979 = (detail_308_694_977 div 8) in 
  let val fltPrm_812_980 = (1 + fltPrm_813_979) in (fltPrm_811_978 * fltPrm_812_980) end end end 
  | Node (wildcard__91_309_695_981 , wildcard__92_310_696_982, lvl_311_697_983, l_312_698_984, r_313_699_985) => 
  let val fltPrm_815_986 = (lvl_311_697_983 + 1) in 
  let val fltPrm_816_987 = (lbDeuxLoadProxy l_312_698_984) in 
  let val fltPrm_814_988 = (fltPrm_815_986 + fltPrm_816_987) in 
  let val fltPrm_817_989 = (lbDeuxLoadProxy r_313_699_985) in (fltPrm_814_988 + fltPrm_817_989) end end end end);

fun truncateTolViolations (p_295_681_961 , tol_296_682_962) = (case p_295_681_961 of Leaf (wildcard__31_297_683_963 , wildcard__32_298_684_964, d_299_685_965) => 
  let val fltIf_808_966 = (d_299_685_965 > tol_296_682_962) in 
  (if fltIf_808_966 then 1 
   else 0) end 
  | Node (wildcard__36_300_686_967 , wildcard__37_301_687_968, wildcard__38_302_688_969, l_303_689_970, r_304_690_971) => 
  let val fltPrm_809_972 = (truncateTolViolations(l_303_689_970 , tol_296_682_962)) in 
  let val fltPrm_810_973 = (truncateTolViolations(r_304_690_971 , tol_296_682_962)) in (fltPrm_809_972 + fltPrm_810_973) end end);

fun addConstPW (p_285_671_948 , c_286_672_949) = (case p_285_671_948 of Leaf (coeff_287_673_950 , sc_288_674_951, det_289_675_952) => 
  let val fltPkd_805_953 = (coeff_287_673_950 + c_286_672_949) in (Leaf (fltPkd_805_953 , sc_288_674_951, det_289_675_952)) end 
  | Node (d_290_676_954 , v_291_677_955, lvl_292_678_956, l_293_679_957, r_294_680_958) => 
  let val fltPkd_806_959 = (addConstPW(l_293_679_957 , c_286_672_949)) in 
  let val fltPkd_807_960 = (addConstPW(r_294_680_958 , c_286_672_949)) in (Node (d_290_676_954 , v_291_677_955, lvl_292_678_956, fltPkd_806_959, fltPkd_807_960)) end end);

fun diffPW (p_276_662_934) = (case p_276_662_934 of Leaf (coeff_277_663_935 , sc_278_664_936, det_279_665_937) => 
  let val fltIf_800_938 = (sc_278_664_936 = 0) in 
  (if fltIf_800_938 then (Leaf (0 , 0, det_279_665_937)) 
   else 
  let val fltPkd_801_939 = (coeff_277_663_935 * sc_278_664_936) in 
  let val fltPkd_802_940 = (sc_278_664_936 - 1) in (Leaf (fltPkd_801_939 , fltPkd_802_940, det_279_665_937)) end end) end 
  | Node (d_280_666_941 , v_281_667_942, lvl_282_668_943, l_283_669_944, r_284_670_945) => 
  let val fltPkd_803_946 = (diffPW l_283_669_944) in 
  let val fltPkd_804_947 = (diffPW r_284_670_945) in (Node (d_280_666_941 , v_281_667_942, lvl_282_668_943, fltPkd_803_946, fltPkd_804_947)) end end);

fun buildPW (d_266_652_907 , seed_267_653_908) = 
  let val fltIf_783_909 = (d_266_652_907 = 0) in 
  (if fltIf_783_909 then 
  let val fltAppE_786_910 = (mixSeed(seed_267_653_908 , 3)) in 
  let val fltPrm_785_911 = (absI fltAppE_786_910) in 
  let val fltPrm_784_912 = (fltPrm_785_911 mod 29) in 
  let val coeff_268_654_913 = (5 + fltPrm_784_912) in 
  let val fltAppE_789_914 = (mixSeed(seed_267_653_908 , 5)) in 
  let val fltPrm_788_915 = (absI fltAppE_789_914) in 
  let val fltPrm_787_916 = (fltPrm_788_915 mod 12) in 
  let val scale_269_655_917 = (1 + fltPrm_787_916) in 
  let val fltAppE_791_918 = (mixSeed(seed_267_653_908 , 7)) in 
  let val fltPrm_790_919 = (absI fltAppE_791_918) in 
  let val detail_270_656_920 = (fltPrm_790_919 mod 40) in (Leaf (coeff_268_654_913 , scale_269_655_917, detail_270_656_920)) end end end end end end end end end end end 
   else 
  let val fltAppE_793_921 = (mixSeed(seed_267_653_908 , 11)) in 
  let val fltPrm_792_922 = (absI fltAppE_793_921) in 
  let val dim_271_657_923 = (fltPrm_792_922 mod 3) in 
  let val fltAppE_795_924 = (mixSeed(seed_267_653_908 , 13)) in 
  let val fltPrm_794_925 = (absI fltAppE_795_924) in 
  let val cut_272_658_926 = (fltPrm_794_925 mod 1000) in 
  let val fltAppE_796_928 = (d_266_652_907 - 1) in 
  let val fltAppE_797_929 = (mixSeed(seed_267_653_908 , 1)) in 
  let val l_274_660_930 = (buildPW(fltAppE_796_928 , fltAppE_797_929)) in 
  let val fltAppE_798_931 = (d_266_652_907 - 1) in 
  let val fltAppE_799_932 = (mixSeed(seed_267_653_908 , 2)) in 
  let val r_275_661_933 = (buildPW(fltAppE_798_931 , fltAppE_799_932)) in (Node (dim_271_657_923 , cut_272_658_926, d_266_652_907, l_274_660_930, r_275_661_933)) end end end end end end end end end end end end) end;

fun internal_traverse_PW (arg_539_641_896) = (case arg_539_641_896 of Leaf (x_540_642_897 , x_541_643_898, x_542_644_899) => () 
  | Node (x_546_645_900 , x_547_646_901, x_548_647_902, x_549_648_903, x_550_649_904) => 
  let val y_554_650_905 = (internal_traverse_PW x_549_648_903) in 
  let val y_555_651_906 = (internal_traverse_PW x_550_649_904) in () end end);

fun compressMass (p_257_632_885) = (case p_257_632_885 of Leaf (c_258_633_886 , wildcard__45_259_634_887, wildcard__46_260_635_888) => (absI c_258_633_886) 
  | Node (wildcard__50_261_636_889 , wildcard__51_262_637_890, wildcard__52_263_638_891, l_264_639_892, r_265_640_893) => 
  let val fltPrm_781_894 = (compressMass l_264_639_892) in 
  let val fltPrm_782_895 = (compressMass r_265_640_893) in (fltPrm_781_894 + fltPrm_782_895) end end);

fun maxI (a_255_630_882 , b_256_631_883) = 
  let val fltIf_780_884 = (a_255_630_882 > b_256_631_883) in 
  (if fltIf_780_884 then a_255_630_882 
   else b_256_631_883) end;

fun autorefineMaxLevel (p_314_729_1019) = (case p_314_729_1019 of Leaf (wildcard__59_315_730_1020 , s_316_731_1021, wildcard__60_317_732_1022) => s_316_731_1021 
  | Node (wildcard__64_318_733_1023 , wildcard__65_319_734_1024, lvl_320_735_1025, l_321_736_1026, r_322_737_1027) => 
  let val fltAppE_819_1028 = (autorefineMaxLevel l_321_736_1026) in 
  let val fltAppE_820_1029 = (autorefineMaxLevel r_322_737_1027) in 
  let val fltAppE_818_1030 = (maxI(fltAppE_819_1028 , fltAppE_820_1029)) in (maxI(lvl_320_735_1025 , fltAppE_818_1030)) end end end);
val _ = (case 
  let val wildcard__207_210_585_835 = (print "Running Program Piecewise Functions (MADNESS style): ") in 
  let val wildcard__205_211_586_836 = (printsym "NEWLINE") in 
  let val fltPrm_779_837 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_778_838 = (fltPrm_779_837 + 23) in 
  let val pfTree_212_587_839 = (buildPW(fltAppE_778_838 , 17)) in 
  let val wildcard__202_213_588_840 = (printsym "Running pass norm2Estimate (fold, uses=5): ") in 
  let val wildcard__200_214_589_841 = (printsym "NEWLINE") in 
  let val norm_215_590_842 = (iterate (fn () => norm2Estimate pfTree_212_587_839)) in 
  let val wildcard__196_216_591_843 = (printsym "End") in 
  let val wildcard__194_217_592_844 = (printsym "NEWLINE") in 
  let val wildcard__192_218_593_845 = (printsym "Running pass truncateTolViolations (fold, uses=3): ") in 
  let val wildcard__190_219_594_846 = (printsym "NEWLINE") in 
  let val refineCnt_220_595_847 = (iterate (fn () => truncateTolViolations(pfTree_212_587_839 , 18))) in 
  let val wildcard__186_221_596_848 = (printsym "End") in 
  let val wildcard__184_222_597_849 = (printsym "NEWLINE") in 
  let val wildcard__182_223_598_850 = (printsym "Running pass compressMass (fold, uses=3): ") in 
  let val wildcard__180_224_599_851 = (printsym "NEWLINE") in 
  let val mass_225_600_852 = (iterate (fn () => compressMass pfTree_212_587_839)) in 
  let val wildcard__176_226_601_853 = (printsym "End") in 
  let val wildcard__174_227_602_854 = (printsym "NEWLINE") in 
  let val wildcard__172_228_603_855 = (printsym "Running pass autorefineMaxLevel (fold, uses=4): ") in 
  let val wildcard__170_229_604_856 = (printsym "NEWLINE") in 
  let val maxLvl_230_605_857 = (iterate (fn () => autorefineMaxLevel pfTree_212_587_839)) in 
  let val wildcard__166_231_606_858 = (printsym "End") in 
  let val wildcard__164_232_607_859 = (printsym "NEWLINE") in 
  let val wildcard__162_233_608_860 = (printsym "Running pass pmapCutHistogram (fold, uses=4): ") in 
  let val wildcard__160_234_609_861 = (printsym "NEWLINE") in 
  let val pmapCuts_235_610_862 = (iterate (fn () => pmapCutHistogram(pfTree_212_587_839 , 500))) in 
  let val wildcard__156_236_611_863 = (printsym "End") in 
  let val wildcard__154_237_612_864 = (printsym "NEWLINE") in 
  let val wildcard__152_238_613_865 = (printsym "Running pass lbDeuxLoadProxy (fold, uses=5): ") in 
  let val wildcard__150_239_614_866 = (printsym "NEWLINE") in 
  let val loadW_240_615_867 = (iterate (fn () => lbDeuxLoadProxy pfTree_212_587_839)) in 
  let val wildcard__146_241_616_868 = (printsym "End") in 
  let val wildcard__144_242_617_869 = (printsym "NEWLINE") in 
  let val wildcard__142_243_618_870 = (printsym "Running pass addConstPW (map, uses=8): ") in 
  let val wildcard__140_244_619_871 = (printsym "NEWLINE") in 
  let val shifted_245_620_872 = (iterate (fn () => addConstPW(pfTree_212_587_839 , 10))) in 
  let val wildcard__136_246_621_873 = (printsym "End") in 
  let val wildcard__134_247_622_874 = (printsym "NEWLINE") in 
  let val wildcard__132_248_623_875 = (printsym "Running pass diffPW (map, uses=8): ") in 
  let val wildcard__130_249_624_876 = (printsym "NEWLINE") in 
  let val internal_diffed_250_625_877 = (iterate (fn () => diffPW shifted_245_620_872)) in 
  let val wildcard__126_251_626_878 = (printsym "End") in 
  let val wildcard__124_252_627_879 = (printsym "NEWLINE") in 
  let val massShift_253_628_880 = (compressMass shifted_245_620_872) in 
  let val massDiff_254_629_881 = (compressMass internal_diffed_250_625_877) in (norm_215_590_842 , refineCnt_220_595_847, mass_225_600_852, maxLvl_230_605_857, pmapCuts_235_610_862, loadW_240_615_867, massShift_253_628_880, massDiff_254_629_881) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7, x__8) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print " "val _ = (print(Int.toString(x__8))) val _ = print ")" in () end);
val _ = print "\n"
