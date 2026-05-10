open GibbonCompat;

datatype dat_Heap = Obj of (int  * int * int *  dat_Heap *  dat_Heap) | Null ;

fun internal_traverse_Heap (arg_525_732_974) = (case arg_525_732_974 of Obj (x_526_733_975 , x_527_734_976, x_528_735_977, x_529_736_978, x_530_737_979) => 
  let val y_534_738_980 = (internal_traverse_Heap x_529_736_978) in 
  let val y_535_739_981 = (internal_traverse_Heap x_530_737_979) in () end end 
  | Null => ());

fun internal_copy_Heap (arg_514_721_963) = (case arg_514_721_963 of Obj (x_515_722_964 , x_516_723_965, x_517_724_966, x_518_725_967, x_519_726_968) => 
  let val y_523_730_972 = (internal_copy_Heap x_518_725_967) in 
  let val y_524_731_973 = (internal_copy_Heap x_519_726_968) in (Obj (x_515_722_964 , x_516_723_965, x_517_724_966, y_523_730_972, y_524_731_973)) end end 
  | Null => Null);

fun deadBytes (h_355_714_952) = (case h_355_714_952 of Obj (wildcard__44_356_715_953 , size_357_716_954, mark_358_717_955, l_359_718_956, r_360_719_957) => 
  let val fltIf_776_958 = (mark_358_717_955 = 0) in 
  let val here_361_720_959 = 
  (if fltIf_776_958 then size_357_716_954 
   else 0) in 
  let val fltPrm_778_960 = (deadBytes l_359_718_956) in 
  let val fltPrm_777_961 = (here_361_720_959 + fltPrm_778_960) in 
  let val fltPrm_779_962 = (deadBytes r_360_719_957) in (fltPrm_777_961 + fltPrm_779_962) end end end end end 
  | Null => 0);

fun countLarge (h_347_706_940 , limit_348_707_941) = (case h_347_706_940 of Obj (wildcard__27_349_708_942 , size_350_709_943, wildcard__28_351_710_944, l_352_711_945, r_353_712_946) => 
  let val fltIf_772_947 = (size_350_709_943 > limit_348_707_941) in 
  let val here_354_713_948 = 
  (if fltIf_772_947 then 1 
   else 0) in 
  let val fltPrm_774_949 = (countLarge(l_352_711_945 , limit_348_707_941)) in 
  let val fltPrm_773_950 = (here_354_713_948 + fltPrm_774_949) in 
  let val fltPrm_775_951 = (countLarge(r_353_712_946 , limit_348_707_941)) in (fltPrm_773_950 + fltPrm_775_951) end end end end end 
  | Null => 0);

fun touchHotObjects (h_336_695_926 , stride_337_696_927, delta_338_697_928) = (case h_336_695_926 of Obj (id_339_698_929 , size_340_699_930, mark_341_700_931, l_342_701_932, r_343_702_933) => 
  let val fltPrm_769_934 = (id_339_698_929 mod stride_337_696_927) in 
  let val hot_344_703_935 = (fltPrm_769_934 = 0) in 
  let val size__345_704_936 = 
  (if hot_344_703_935 then (size_340_699_930 + delta_338_697_928) 
   else size_340_699_930) in 
  let val mark__346_705_937 = 
  (if hot_344_703_935 then 1 
   else mark_341_700_931) in 
  let val fltPkd_770_938 = (touchHotObjects(l_342_701_932 , stride_337_696_927, delta_338_697_928)) in 
  let val fltPkd_771_939 = (touchHotObjects(r_343_702_933 , stride_337_696_927, delta_338_697_928)) in (Obj (id_339_698_929 , size__345_704_936, mark__346_705_937, fltPkd_770_938, fltPkd_771_939)) end end end end end end 
  | Null => Null);

fun internal_print_Heap (arg_536_675_906) = (case arg_536_675_906 of Obj (x_537_676_907 , x_538_677_908, x_539_678_909, x_540_679_910, x_541_680_911) => 
  let val wildcard_547_681_912 = (print "(Obj") in 
  let val wildcard_553_682_913 = (print " ") in 
  let val y_542_683_914 = (print(Int.toString(x_537_676_907))) in 
  let val wildcard_552_684_915 = (print " ") in 
  let val y_543_685_916 = (print(Int.toString(x_538_677_908))) in 
  let val wildcard_551_686_917 = (print " ") in 
  let val y_544_687_918 = (print(Int.toString(x_539_678_909))) in 
  let val wildcard_550_688_919 = (print " ") in 
  let val y_545_689_920 = (internal_print_Heap x_540_679_910) in 
  let val wildcard_549_690_921 = (print " ") in 
  let val y_546_691_922 = (internal_print_Heap x_541_680_911) in 
  let val wildcard_548_692_923 = (print ")") in () end end end end end end end end end end end end 
  | Null => 
  let val wildcard_554_693_924 = (print "(Null") in 
  let val wildcard_555_694_925 = (print ")") in () end end);

fun sweepUnmarked (h_320_659_896) = (case h_320_659_896 of Obj (id_321_660_897 , size_322_661_898, mark_323_662_899, l_324_663_900, r_325_664_901) => 
  let val fltIf_766_902 = (mark_323_662_899 = 1) in 
  let val size__326_665_903 = 
  (if fltIf_766_902 then size_322_661_898 
   else 0) in 
  let val fltPkd_767_904 = (sweepUnmarked l_324_663_900) in 
  let val fltPkd_768_905 = (sweepUnmarked r_325_664_901) in (Obj (id_321_660_897 , size__326_665_903, 0, fltPkd_767_904, fltPkd_768_905)) end end end end 
  | Null => Null);

fun sumObjIds (h_314_653_887) = (case h_314_653_887 of Obj (id_315_654_888 , wildcard__61_316_655_889, wildcard__62_317_656_890, l_318_657_891, r_319_658_892) => 
  let val fltPrm_764_893 = (sumObjIds l_318_657_891) in 
  let val fltPrm_763_894 = (id_315_654_888 + fltPrm_764_893) in 
  let val fltPrm_765_895 = (sumObjIds r_319_658_892) in (fltPrm_763_894 + fltPrm_765_895) end end end 
  | Null => 0);

fun totalHeapSize (h_308_647_878) = (case h_308_647_878 of Obj (wildcard__9_309_648_879 , size_310_649_880, wildcard__10_311_650_881, l_312_651_882, r_313_652_883) => 
  let val fltPrm_761_884 = (totalHeapSize l_312_651_882) in 
  let val fltPrm_760_885 = (size_310_649_880 + fltPrm_761_884) in 
  let val fltPrm_762_886 = (totalHeapSize r_313_652_883) in (fltPrm_760_885 + fltPrm_762_886) end end end 
  | Null => 0);

fun buildHeap (d_302_641_867) = 
  let val fltIf_755_868 = (d_302_641_867 = 0) in 
  (if fltIf_755_868 then Null 
   else 
  let val size_304_643_870 = (d_302_641_867 * 10) in 
  let val fltPrm_757_871 = (d_302_641_867 div 2) in 
  let val fltPrm_756_872 = (fltPrm_757_871 * 2) in 
  let val mark_305_644_873 = (d_302_641_867 - fltPrm_756_872) in 
  let val fltAppE_758_874 = (d_302_641_867 - 1) in 
  let val l_306_645_875 = (buildHeap fltAppE_758_874) in 
  let val fltAppE_759_876 = (d_302_641_867 - 1) in 
  let val r_307_646_877 = (buildHeap fltAppE_759_876) in (Obj (d_302_641_867 , size_304_643_870, mark_305_644_873, l_306_645_875, r_307_646_877)) end end end end end end end end) end;

fun countSurvivors (h_294_633_854 , maxSize_295_634_855) = (case h_294_633_854 of Obj (wildcard__53_296_635_856 , size_297_636_857, mark_298_637_858, l_299_638_859, r_300_639_860) => 
  let val fltIf_750_861 = (mark_298_637_858 = 1) in 
  let val here_301_640_863 = 
  (if fltIf_750_861 then 
  let val fltIf_751_862 = (size_297_636_857 <= maxSize_295_634_855) in 
  (if fltIf_751_862 then 1 
   else 0) end 
   else 0) in 
  let val fltPrm_753_864 = (countSurvivors(l_299_638_859 , maxSize_295_634_855)) in 
  let val fltPrm_752_865 = (here_301_640_863 + fltPrm_753_864) in 
  let val fltPrm_754_866 = (countSurvivors(r_300_639_860 , maxSize_295_634_855)) in (fltPrm_752_865 + fltPrm_754_866) end end end end end 
  | Null => 0);

fun countMarked (h_280_619_843) = (case h_280_619_843 of Obj (wildcard__17_281_620_844 , wildcard__18_282_621_845, mark_283_622_846, l_284_623_847, r_285_624_848) => 
  let val fltIf_746_849 = (mark_283_622_846 = 1) in 
  let val here_286_625_850 = 
  (if fltIf_746_849 then 1 
   else 0) in 
  let val fltPrm_748_851 = (countMarked l_284_623_847) in 
  let val fltPrm_747_852 = (here_286_625_850 + fltPrm_748_851) in 
  let val fltPrm_749_853 = (countMarked r_285_624_848) in (fltPrm_747_852 + fltPrm_749_853) end end end end end 
  | Null => 0);

fun liveBytes (h_273_612_832) = (case h_273_612_832 of Obj (wildcard__36_274_613_833 , size_275_614_834, mark_276_615_835, l_277_616_836, r_278_617_837) => 
  let val fltIf_742_838 = (mark_276_615_835 = 1) in 
  let val here_279_618_839 = 
  (if fltIf_742_838 then size_275_614_834 
   else 0) in 
  let val fltPrm_744_840 = (liveBytes l_277_616_836) in 
  let val fltPrm_743_841 = (here_279_618_839 + fltPrm_744_840) in 
  let val fltPrm_745_842 = (liveBytes r_278_617_837) in (fltPrm_743_841 + fltPrm_745_842) end end end end end 
  | Null => 0);
val _ = (case 
  let val wildcard__214_217_556_780 = (printsym "Running program ObjectGraph Simulated a GC Program: ") in 
  let val wildcard__212_218_557_781 = (printsym "NEWLINE") in 
  let val fltPrm_741_782 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_740_783 = (fltPrm_741_782 + 23) in 
  let val heap_219_558_784 = (buildHeap fltAppE_740_783) in 
  let val wildcard__209_220_559_785 = (printsym "Running pass totalHeapSize (fold, uses=3): ") in 
  let val wildcard__207_221_560_786 = (printsym "NEWLINE") in 
  let val heapSize_222_561_787 = (iterate (fn () => totalHeapSize heap_219_558_784)) in 
  let val wildcard__203_223_562_788 = (printsym "End") in 
  let val wildcard__201_224_563_789 = (printsym "NEWLINE") in 
  let val wildcard__199_225_564_790 = (printsym "Running pass countMarked (fold, uses=3): ") in 
  let val wildcard__197_226_565_791 = (printsym "NEWLINE") in 
  let val countMarkedItems_227_566_792 = (iterate (fn () => countMarked heap_219_558_784)) in 
  let val wildcard__193_228_567_793 = (printsym "End") in 
  let val wildcard__191_229_568_794 = (printsym "NEWLINE") in 
  let val wildcard__189_230_569_795 = (printsym "Running pass countLargeItems (fold, uses=3): ") in 
  let val wildcard__187_231_570_796 = (printsym "NEWLINE") in 
  let val countLargeItems_232_571_797 = (iterate (fn () => countLarge(heap_219_558_784 , 100))) in 
  let val wildcard__183_233_572_798 = (printsym "End") in 
  let val wildcard__181_234_573_799 = (printsym "NEWLINE") in 
  let val wildcard__179_235_574_800 = (printsym "Running pass liveBytes (fold, uses=4): ") in 
  let val wildcard__177_236_575_801 = (printsym "NEWLINE") in 
  let val liveSet_237_576_802 = (iterate (fn () => liveBytes heap_219_558_784)) in 
  let val wildcard__173_238_577_803 = (printsym "End") in 
  let val wildcard__171_239_578_804 = (printsym "NEWLINE") in 
  let val wildcard__169_240_579_805 = (printsym "Running pass deadBytes (fold, uses=4): ") in 
  let val wildcard__167_241_580_806 = (printsym "NEWLINE") in 
  let val reclaimable_242_581_807 = (iterate (fn () => deadBytes heap_219_558_784)) in 
  let val wildcard__163_243_582_808 = (printsym "End") in 
  let val wildcard__161_244_583_809 = (printsym "NEWLINE") in 
  let val wildcard__159_245_584_810 = (printsym "Running pass countSurvivors (fold, uses=4): ") in 
  let val wildcard__157_246_585_811 = (printsym "NEWLINE") in 
  let val survivors_247_586_812 = (iterate (fn () => countSurvivors(heap_219_558_784 , 120))) in 
  let val wildcard__153_248_587_813 = (printsym "End") in 
  let val wildcard__151_249_588_814 = (printsym "NEWLINE") in 
  let val wildcard__149_250_589_815 = (printsym "Running pass sumObjIds (fold, uses=3): ") in 
  let val wildcard__147_251_590_816 = (printsym "NEWLINE") in 
  let val sObjIds_252_591_817 = (iterate (fn () => sumObjIds heap_219_558_784)) in 
  let val wildcard__143_253_592_818 = (printsym "End") in 
  let val wildcard__141_254_593_819 = (printsym "NEWLINE") in 
  let val wildcard__139_255_594_820 = (printsym "Running pass sweepUnmarked (map, uses=5): ") in 
  let val wildcard__137_256_595_821 = (printsym "NEWLINE") in 
  let val heapSwept_257_596_822 = (iterate (fn () => sweepUnmarked heap_219_558_784)) in 
  let val wildcard__133_258_597_823 = (printsym "End") in 
  let val wildcard__131_259_598_824 = (printsym "NEWLINE") in 
  let val wildcard__129_260_599_825 = (printsym "Running pass touchHotObjects (map, uses=5): ") in 
  let val wildcard__127_261_600_826 = (printsym "NEWLINE") in 
  let val heapHot_262_601_827 = (iterate (fn () => touchHotObjects(heap_219_558_784 , 4, 12))) in 
  let val wildcard__123_263_602_828 = (printsym "End") in 
  let val wildcard__121_264_603_829 = (printsym "NEWLINE") in 
  let val liveSwept_265_604_830 = (liveBytes heapSwept_257_596_822) in 
  let val liveHot_266_605_831 = (liveBytes heapHot_262_601_827) in (heapSize_222_561_787 , countMarkedItems_227_566_792, countLargeItems_232_571_797, liveSet_237_576_802, reclaimable_242_581_807, survivors_247_586_812, sObjIds_252_591_817, liveSwept_265_604_830, liveHot_266_605_831) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7, x__8, x__9) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print " "val _ = (print(Int.toString(x__8))) val _ = print " "val _ = (print(Int.toString(x__9))) val _ = print ")" in () end);
val _ = print "\n"
