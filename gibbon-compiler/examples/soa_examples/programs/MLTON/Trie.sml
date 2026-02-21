open GibbonCompat;

datatype dat_Trie = TNode of (int  * int * int * int *  dat_Trie *  dat_Trie) | TLeaf of (int  * int * int * int)| TEmpty ;

fun internal_copy_Trie (arg_534_802_1126) = (case arg_534_802_1126 of TNode (x_535_803_1127 , x_536_804_1128, x_537_805_1129, x_538_806_1130, x_539_807_1131, x_540_808_1132) => 
  let val y_545_813_1137 = (internal_copy_Trie x_539_807_1131) in 
  let val y_546_814_1138 = (internal_copy_Trie x_540_808_1132) in (TNode (x_535_803_1127 , x_536_804_1128, x_537_805_1129, x_538_806_1130, y_545_813_1137, y_546_814_1138)) end end 
  | TLeaf (x_547_815_1139 , x_548_816_1140, x_549_817_1141, x_550_818_1142) => (TLeaf (x_547_815_1139 , x_548_816_1140, x_549_817_1141, x_550_818_1142))
  | TEmpty => TEmpty);

fun internal_traverse_Trie (arg_555_789_1113) = (case arg_555_789_1113 of TNode (x_556_790_1114 , x_557_791_1115, x_558_792_1116, x_559_793_1117, x_560_794_1118, x_561_795_1119) => 
  let val y_566_796_1120 = (internal_traverse_Trie x_560_794_1118) in 
  let val y_567_797_1121 = (internal_traverse_Trie x_561_795_1119) in () end end 
  | TLeaf (x_568_798_1122 , x_569_799_1123, x_570_800_1124, x_571_801_1125) => ()
  | TEmpty => ());

fun sumPrefixFreq (t_347_778_1099) = (case t_347_778_1099 of TNode (wildcard__18_348_779_1100 , f_349_780_1101, wildcard__19_350_781_1102, wildcard__20_351_782_1103, l_352_783_1104, r_353_784_1105) => 
  let val fltPrm_878_1106 = (sumPrefixFreq l_352_783_1104) in 
  let val fltPrm_877_1107 = (f_349_780_1101 + fltPrm_878_1106) in 
  let val fltPrm_879_1108 = (sumPrefixFreq r_353_784_1105) in (fltPrm_877_1107 + fltPrm_879_1108) end end end 
  | TLeaf (wildcard__27_354_785_1109 , wildcard__28_355_786_1110, wildcard__29_356_787_1111, wildcard__30_357_788_1112) => 0
  | TEmpty => 0);

fun decayTrieStats (t_332_763_1078 , k_333_764_1079) = (case t_332_763_1078 of TNode (c_334_765_1080 , f_335_766_1081, sc_336_767_1082, fl_337_768_1083, l_338_769_1084, r_339_770_1085) => 
  let val fltPrm_871_1086 = (f_335_766_1081 * k_333_764_1079) in 
  let val f2_340_771_1087 = (fltPrm_871_1086 div 10) in 
  let val fltPrm_873_1088 = (k_333_764_1079 + 1) in 
  let val fltPrm_872_1089 = (sc_336_767_1082 * fltPrm_873_1088) in 
  let val sc2_341_772_1090 = (fltPrm_872_1089 div 10) in 
  let val fltPkd_874_1091 = (decayTrieStats(l_338_769_1084 , k_333_764_1079)) in 
  let val fltPkd_875_1092 = (decayTrieStats(r_339_770_1085 , k_333_764_1079)) in (TNode (c_334_765_1080 , f2_340_771_1087, sc2_341_772_1090, fl_337_768_1083, fltPkd_874_1091, fltPkd_875_1092)) end end end end end end end 
  | TLeaf (term_342_773_1093 , wid_343_774_1094, score_344_775_1095, meta_345_776_1096) => 
  let val fltPrm_876_1097 = (score_344_775_1095 * k_333_764_1079) in 
  let val s2_346_777_1098 = (fltPrm_876_1097 div 10) in (TLeaf (term_342_773_1093 , wid_343_774_1094, s2_346_777_1098, meta_345_776_1096)) end end
  | TEmpty => TEmpty);

fun countLazyNodes (t_319_750_1060 , metaCut_320_751_1061) = (case t_319_750_1060 of TNode (wildcard__90_321_752_1062 , wildcard__91_322_753_1063, wildcard__92_323_754_1064, fl_324_755_1065, l_325_756_1066, r_326_757_1067) => 
  let val fltIf_866_1068 = (fl_324_755_1065 = 0) in 
  let val here_327_758_1069 = 
  (if fltIf_866_1068 then 1 
   else 0) in 
  let val fltPrm_868_1070 = (countLazyNodes(l_325_756_1066 , metaCut_320_751_1061)) in 
  let val fltPrm_867_1071 = (here_327_758_1069 + fltPrm_868_1070) in 
  let val fltPrm_869_1072 = (countLazyNodes(r_326_757_1067 , metaCut_320_751_1061)) in (fltPrm_867_1071 + fltPrm_869_1072) end end end end end 
  | TLeaf (wildcard__100_328_759_1073 , wildcard__101_329_760_1074, wildcard__102_330_761_1075, meta_331_762_1076) => 
  let val fltIf_870_1077 = (meta_331_762_1076 < metaCut_320_751_1061) in 
  (if fltIf_870_1077 then 1 
   else 0) end
  | TEmpty => 0);

fun absI (x_318_749_1058) = 
  let val fltIf_865_1059 = (x_318_749_1058 < 0) in 
  (if fltIf_865_1059 then (0 - x_318_749_1058) 
   else x_318_749_1058) end;

fun mixSeed (s_316_747_1053 , salt_317_748_1054) = 
  let val fltPrm_863_1055 = (s_316_747_1053 * 1103) in 
  let val fltPrm_864_1056 = (salt_317_748_1054 * 97) in 
  let val fltPrm_862_1057 = (fltPrm_863_1055 + fltPrm_864_1056) in (fltPrm_862_1057 + 13) end end end;

fun countTerminals (t_305_736_1040) = (case t_305_736_1040 of TLeaf (term_306_737_1041 , wildcard__36_307_738_1042, wildcard__37_308_739_1043, wildcard__38_309_740_1044) => term_306_737_1041 
  | TNode (wildcard__43_310_741_1045 , wildcard__44_311_742_1046, wildcard__45_312_743_1047, wildcard__46_313_744_1048, l_314_745_1049, r_315_746_1050) => 
  let val fltPrm_860_1051 = (countTerminals l_314_745_1049) in 
  let val fltPrm_861_1052 = (countTerminals r_315_746_1050) in (fltPrm_860_1051 + fltPrm_861_1052) end end
  | TEmpty => 0);

fun autocompleteTopKProxy (t_293_724_1024 , minScore_294_725_1025) = (case t_293_724_1024 of TLeaf (term_295_726_1026 , wildcard__73_296_727_1027, score_297_728_1028, wildcard__74_298_729_1029) => 
  let val fltIf_856_1030 = (score_297_728_1028 >= minScore_294_725_1025) in 
  (if fltIf_856_1030 then (term_295_726_1026 * score_297_728_1028) 
   else 0) end 
  | TNode (wildcard__79_299_730_1031 , freq_300_731_1032, wildcard__80_301_732_1033, wildcard__81_302_733_1034, l_303_734_1035, r_304_735_1036) => 
  let val fltPrm_858_1037 = (autocompleteTopKProxy(l_303_734_1035 , minScore_294_725_1025)) in 
  let val fltPrm_857_1038 = (freq_300_731_1032 + fltPrm_858_1037) in 
  let val fltPrm_859_1039 = (autocompleteTopKProxy(r_304_735_1036 , minScore_294_725_1025)) in (fltPrm_857_1038 + fltPrm_859_1039) end end end
  | TEmpty => 0);

fun resetTraversalState (t_282_713_1011) = (case t_282_713_1011 of TNode (c_283_714_1012 , f_284_715_1013, sc_285_716_1014, wildcard__126_286_717_1015, l_287_718_1016, r_288_719_1017) => 
  let val fltPkd_854_1018 = (resetTraversalState l_287_718_1016) in 
  let val fltPkd_855_1019 = (resetTraversalState r_288_719_1017) in (TNode (c_283_714_1012 , f_284_715_1013, sc_285_716_1014, 0, fltPkd_854_1018, fltPkd_855_1019)) end end 
  | TLeaf (term_289_720_1020 , wid_290_721_1021, score_291_722_1022, wildcard__134_292_723_1023) => (TLeaf (term_289_720_1020 , wid_290_721_1021, score_291_722_1022, 0))
  | TEmpty => TEmpty);

fun sumSubtreeHints (t_271_702_997) = (case t_271_702_997 of TNode (wildcard__54_272_703_998 , wildcard__55_273_704_999, sc_274_705_1000, wildcard__56_275_706_1001, l_276_707_1002, r_277_708_1003) => 
  let val fltPrm_852_1004 = (sumSubtreeHints l_276_707_1002) in 
  let val fltPrm_851_1005 = (sc_274_705_1000 + fltPrm_852_1004) in 
  let val fltPrm_853_1006 = (sumSubtreeHints r_277_708_1003) in (fltPrm_851_1005 + fltPrm_853_1006) end end end 
  | TLeaf (wildcard__63_278_709_1007 , wildcard__64_279_710_1008, wildcard__65_280_711_1009, wildcard__66_281_712_1010) => 0
  | TEmpty => 0);

fun internal_print_Trie (arg_576_665_960) = (case arg_576_665_960 of TNode (x_577_666_961 , x_578_667_962, x_579_668_963, x_580_669_964, x_581_670_965, x_582_671_966) => 
  let val wildcard_589_672_967 = (print "(TNode") in 
  let val wildcard_596_673_968 = (print " ") in 
  let val y_583_674_969 = (print(Int.toString(x_577_666_961))) in 
  let val wildcard_595_675_970 = (print " ") in 
  let val y_584_676_971 = (print(Int.toString(x_578_667_962))) in 
  let val wildcard_594_677_972 = (print " ") in 
  let val y_585_678_973 = (print(Int.toString(x_579_668_963))) in 
  let val wildcard_593_679_974 = (print " ") in 
  let val y_586_680_975 = (print(Int.toString(x_580_669_964))) in 
  let val wildcard_592_681_976 = (print " ") in 
  let val y_587_682_977 = (internal_print_Trie x_581_670_965) in 
  let val wildcard_591_683_978 = (print " ") in 
  let val y_588_684_979 = (internal_print_Trie x_582_671_966) in 
  let val wildcard_590_685_980 = (print ")") in () end end end end end end end end end end end end end end 
  | TLeaf (x_597_686_981 , x_598_687_982, x_599_688_983, x_600_689_984) => 
  let val wildcard_605_690_985 = (print "(TLeaf") in 
  let val wildcard_610_691_986 = (print " ") in 
  let val y_601_692_987 = (print(Int.toString(x_597_686_981))) in 
  let val wildcard_609_693_988 = (print " ") in 
  let val y_602_694_989 = (print(Int.toString(x_598_687_982))) in 
  let val wildcard_608_695_990 = (print " ") in 
  let val y_603_696_991 = (print(Int.toString(x_599_688_983))) in 
  let val wildcard_607_697_992 = (print " ") in 
  let val y_604_698_993 = (print(Int.toString(x_600_689_984))) in 
  let val wildcard_606_699_994 = (print ")") in () end end end end end end end end end end
  | TEmpty => 
  let val wildcard_611_700_995 = (print "(TEmpty") in 
  let val wildcard_612_701_996 = (print ")") in () end end);

fun buildTrie (d_259_653_922 , seed_260_654_923) = 
  let val fltIf_825_924 = (d_259_653_922 = 0) in 
  (if fltIf_825_924 then 
  let val fltAppE_828_925 = (mixSeed(seed_260_654_923 , 2)) in 
  let val fltPrm_827_926 = (absI fltAppE_828_925) in 
  let val fltPrm_826_927 = (fltPrm_827_926 mod 3) in 
  let val term_261_655_928 = (1 + fltPrm_826_927) in 
  let val fltAppE_830_929 = (mixSeed(seed_260_654_923 , 3)) in 
  let val fltPrm_829_930 = (absI fltAppE_830_929) in 
  let val wid_262_656_931 = (fltPrm_829_930 mod 100000) in 
  let val fltAppE_833_932 = (mixSeed(seed_260_654_923 , 5)) in 
  let val fltPrm_832_933 = (absI fltAppE_833_932) in 
  let val fltPrm_831_934 = (fltPrm_832_933 mod 95) in 
  let val scr_263_657_935 = (5 + fltPrm_831_934) in 
  let val fltAppE_835_936 = (mixSeed(seed_260_654_923 , 7)) in 
  let val fltPrm_834_937 = (absI fltAppE_835_936) in 
  let val meta_264_658_938 = (fltPrm_834_937 mod 16) in (TLeaf (term_261_655_928 , wid_262_656_931, scr_263_657_935, meta_264_658_938)) end end end end end end end end end end end end end end 
   else 
  let val fltAppE_837_939 = (mixSeed(seed_260_654_923 , 11)) in 
  let val fltPrm_836_940 = (absI fltAppE_837_939) in 
  let val c_265_659_941 = (fltPrm_836_940 mod 26) in 
  let val fltAppE_840_942 = (mixSeed(seed_260_654_923 , 13)) in 
  let val fltPrm_839_943 = (absI fltAppE_840_942) in 
  let val fltPrm_838_944 = (fltPrm_839_943 mod 120) in 
  let val pf_266_660_945 = (1 + fltPrm_838_944) in 
  let val fltAppE_844_946 = (mixSeed(seed_260_654_923 , 17)) in 
  let val fltPrm_843_947 = (absI fltAppE_844_946) in 
  let val fltPrm_842_948 = (fltPrm_843_947 mod 80) in 
  let val fltPrm_841_949 = (1 + fltPrm_842_948) in 
  let val sc_267_661_950 = (2 * fltPrm_841_949) in 
  let val fltAppE_846_951 = (mixSeed(seed_260_654_923 , 19)) in 
  let val fltPrm_845_952 = (absI fltAppE_846_951) in 
  let val fl_268_662_953 = (fltPrm_845_952 mod 4) in 
  let val fltAppE_847_954 = (d_259_653_922 - 1) in 
  let val fltAppE_848_955 = (mixSeed(seed_260_654_923 , 23)) in 
  let val l_269_663_956 = (buildTrie(fltAppE_847_954 , fltAppE_848_955)) in 
  let val fltAppE_849_957 = (d_259_653_922 - 1) in 
  let val fltAppE_850_958 = (mixSeed(seed_260_654_923 , 29)) in 
  let val r_270_664_959 = (buildTrie(fltAppE_849_957 , fltAppE_850_958)) in (TNode (c_265_659_941 , pf_266_660_945, sc_267_661_950, fl_268_662_953, l_269_663_956, r_270_664_959)) end end end end end end end end end end end end end end end end end end end end end) end;
val _ = (case 
  let val wildcard__216_219_613_880 = (printsym "Running program Trie: ") in 
  let val wildcard__214_220_614_881 = (printsym "NEWLINE") in 
  let val fltPrm_824_882 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_823_883 = (fltPrm_824_882 + 22) in 
  let val trie_221_615_884 = (buildTrie(fltAppE_823_883 , 17)) in 
  let val wildcard__211_222_616_885 = (printsym "Running pass sumPrefixFreq (fold, uses=3): ") in 
  let val wildcard__209_223_617_886 = (printsym "NEWLINE") in 
  let val totFreq_224_618_887 = (iterate (fn () => sumPrefixFreq trie_221_615_884)) in 
  let val wildcard__205_225_619_888 = (printsym "End") in 
  let val wildcard__203_226_620_889 = (printsym "NEWLINE") in 
  let val wildcard__201_227_621_890 = (printsym "Running pass countTerminals (fold, uses=3): ") in 
  let val wildcard__199_228_622_891 = (printsym "NEWLINE") in 
  let val totTerms_229_623_892 = (iterate (fn () => countTerminals trie_221_615_884)) in 
  let val wildcard__195_230_624_893 = (printsym "End") in 
  let val wildcard__193_231_625_894 = (printsym "NEWLINE") in 
  let val wildcard__191_232_626_895 = (printsym "Running pass sumSubtreeHints (fold, uses=3): ") in 
  let val wildcard__189_233_627_896 = (printsym "NEWLINE") in 
  let val hintSum_234_628_897 = (iterate (fn () => sumSubtreeHints trie_221_615_884)) in 
  let val wildcard__185_235_629_898 = (printsym "End") in 
  let val wildcard__183_236_630_899 = (printsym "NEWLINE") in 
  let val wildcard__181_237_631_900 = (printsym "Running pass autocompleteTopKProxy (fold, uses=5): ") in 
  let val wildcard__179_238_632_901 = (printsym "NEWLINE") in 
  let val topK_239_633_902 = (iterate (fn () => autocompleteTopKProxy(trie_221_615_884 , 40))) in 
  let val wildcard__175_240_634_903 = (printsym "End") in 
  let val wildcard__173_241_635_904 = (printsym "NEWLINE") in 
  let val wildcard__171_242_636_905 = (printsym "Running pass countLazyNodes (fold, uses=4): ") in 
  let val wildcard__169_243_637_906 = (printsym "NEWLINE") in 
  let val lazyN_244_638_907 = (iterate (fn () => countLazyNodes(trie_221_615_884 , 4))) in 
  let val wildcard__165_245_639_908 = (printsym "End") in 
  let val wildcard__163_246_640_909 = (printsym "NEWLINE") in 
  let val wildcard__161_247_641_910 = (printsym "Running pass decayTrieStats (map, uses=10): ") in 
  let val wildcard__159_248_642_911 = (printsym "NEWLINE") in 
  let val trie__249_643_912 = (iterate (fn () => decayTrieStats(trie_221_615_884 , 9))) in 
  let val wildcard__155_250_644_913 = (printsym "End") in 
  let val wildcard__153_251_645_914 = (printsym "NEWLINE") in 
  let val wildcard__151_252_646_915 = (printsym "Running pass resetTraversalState (map, uses=10): ") in 
  let val wildcard__149_253_647_916 = (printsym "NEWLINE") in 
  let val trie___254_648_917 = (iterate (fn () => resetTraversalState trie__249_643_912)) in 
  let val wildcard__145_255_649_918 = (printsym "End") in 
  let val wildcard__143_256_650_919 = (printsym "NEWLINE") in 
  let val decayedFreq_257_651_920 = (sumPrefixFreq trie__249_643_912) in 
  let val resetFreq_258_652_921 = (sumPrefixFreq trie___254_648_917) in (totFreq_224_618_887 , totTerms_229_623_892, hintSum_234_628_897, topK_239_633_902, lazyN_244_638_907, decayedFreq_257_651_920, resetFreq_258_652_921) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print ")" in () end);
val _ = print "\n"
