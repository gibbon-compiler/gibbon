open GibbonCompat;

datatype dat_List = Cons of (int  * int * int * int * int * int * int * int * int * int *  dat_List) | Nil ;

fun internal_copy_List (arg_72_230_331) = (case arg_72_230_331 of Cons (x_73_231_332 , x_74_232_333, x_75_233_334, x_76_234_335, x_77_235_336, x_78_236_337, x_79_237_338, x_80_238_339, x_81_239_340, x_82_240_341, x_83_241_342) => 
  let val y_94_252_353 = (internal_copy_List x_83_241_342) in (Cons (x_73_231_332 , x_74_232_333, x_75_233_334, x_76_234_335, x_77_235_336, x_78_236_337, x_79_237_338, x_80_238_339, x_81_239_340, x_82_240_341, y_94_252_353)) end 
  | Nil => Nil);

fun reduce (lst_43_217_318) = (case lst_43_217_318 of Nil => 0 
  | Cons (a_44_218_319 , b_45_219_320, c_46_220_321, d_47_221_322, e_48_222_323, f_49_223_324, g_50_224_325, h_51_225_326, e_52_226_327, f_53_227_328, rst_54_228_329) => 
  let val sumRst_55_229_330 = (reduce rst_54_228_329) in (a_44_218_319 + sumRst_55_229_330) end);

fun mkList (len_41_215_314) = 
  let val fltIf_253_315 = (len_41_215_314 < 0) in 
  (if fltIf_253_315 then Nil 
   else 
  let val fltAppE_254_316 = (len_41_215_314 - 1) in 
  let val rst_42_216_317 = (mkList fltAppE_254_316) in (Cons (len_41_215_314 , len_41_215_314, len_41_215_314, len_41_215_314, len_41_215_314, len_41_215_314, len_41_215_314, len_41_215_314, len_41_215_314, len_41_215_314, rst_42_216_317)) end end) end;

fun internal_traverse_List (arg_95_202_301) = (case arg_95_202_301 of Cons (x_96_203_302 , x_97_204_303, x_98_205_304, x_99_206_305, x_100_207_306, x_101_208_307, x_102_209_308, x_103_210_309, x_104_211_310, x_105_212_311, x_106_213_312) => 
  let val y_117_214_313 = (internal_traverse_List x_106_213_312) in () end 
  | Nil => ());

fun internal_print_List (arg_118_164_263) = (case arg_118_164_263 of Cons (x_119_165_264 , x_120_166_265, x_121_167_266, x_122_168_267, x_123_169_268, x_124_170_269, x_125_171_270, x_126_172_271, x_127_173_272, x_128_174_273, x_129_175_274) => 
  let val wildcard_141_176_275 = (print "(Cons") in 
  let val wildcard_153_177_276 = (print " ") in 
  let val y_130_178_277 = (print(Int.toString(x_119_165_264))) in 
  let val wildcard_152_179_278 = (print " ") in 
  let val y_131_180_279 = (print(Int.toString(x_120_166_265))) in 
  let val wildcard_151_181_280 = (print " ") in 
  let val y_132_182_281 = (print(Int.toString(x_121_167_266))) in 
  let val wildcard_150_183_282 = (print " ") in 
  let val y_133_184_283 = (print(Int.toString(x_122_168_267))) in 
  let val wildcard_149_185_284 = (print " ") in 
  let val y_134_186_285 = (print(Int.toString(x_123_169_268))) in 
  let val wildcard_148_187_286 = (print " ") in 
  let val y_135_188_287 = (print(Int.toString(x_124_170_269))) in 
  let val wildcard_147_189_288 = (print " ") in 
  let val y_136_190_289 = (print(Int.toString(x_125_171_270))) in 
  let val wildcard_146_191_290 = (print " ") in 
  let val y_137_192_291 = (print(Int.toString(x_126_172_271))) in 
  let val wildcard_145_193_292 = (print " ") in 
  let val y_138_194_293 = (print(Int.toString(x_127_173_272))) in 
  let val wildcard_144_195_294 = (print " ") in 
  let val y_139_196_295 = (print(Int.toString(x_128_174_273))) in 
  let val wildcard_143_197_296 = (print " ") in 
  let val y_140_198_297 = (internal_print_List x_129_175_274) in 
  let val wildcard_142_199_298 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end 
  | Nil => 
  let val wildcard_154_200_299 = (print "(Nil") in 
  let val wildcard_155_201_300 = (print ")") in () end end);
val _ = (print(Int.toString(
  let val wildcard__30_33_156_255 = (printsym "Running program recution on List with 10 Integer elements: ") in 
  let val wildcard__28_34_157_256 = (printsym "NEWLINE") in 
  let val lst_35_158_257 = (mkList 10000000) in 
  let val wildcard__25_36_159_258 = (printsym "Running pass reduction (fold, uses=2): ") in 
  let val wildcard__23_37_160_259 = (printsym "NEWLINE") in 
  let val sum_38_161_260 = (reduce lst_35_158_257) in 
  let val wildcard__19_39_162_261 = (printsym "End") in 
  let val wildcard__17_40_163_262 = (printsym "NEWLINE") in sum_38_161_260 end end end end end end end end)));
val _ = print "\n"
