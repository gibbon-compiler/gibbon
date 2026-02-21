open GibbonCompat;

datatype dat_Tree = Leaf of (int) | Node of (int  *  dat_Tree *  dat_Tree *  dat_Tree) ;

fun internal_print_Tree (arg_157_230_330) = (case arg_157_230_330 of Leaf (x_158_231_331) => 
  let val wildcard_160_232_332 = (print "(Leaf") in 
  let val wildcard_162_233_333 = (print " ") in 
  let val y_159_234_334 = (print(Int.toString(x_158_231_331))) in 
  let val wildcard_161_235_335 = (print ")") in () end end end end 
  | Node (x_163_236_336 , x_164_237_337, x_165_238_338, x_166_239_339) => 
  let val wildcard_171_240_340 = (print "(Node") in 
  let val wildcard_176_241_341 = (print " ") in 
  let val y_167_242_342 = (print(Int.toString(x_163_236_336))) in 
  let val wildcard_175_243_343 = (print " ") in 
  let val y_168_244_344 = (internal_print_Tree x_164_237_337) in 
  let val wildcard_174_245_345 = (print " ") in 
  let val y_169_246_346 = (internal_print_Tree x_165_238_338) in 
  let val wildcard_173_247_347 = (print " ") in 
  let val y_170_248_348 = (internal_print_Tree x_166_239_339) in 
  let val wildcard_172_249_349 = (print ")") in () end end end end end end end end end end);

fun internal_traverse_Tree (arg_146_221_321) = (case arg_146_221_321 of Leaf (x_147_222_322) => () 
  | Node (x_149_223_323 , x_150_224_324, x_151_225_325, x_152_226_326) => 
  let val y_154_227_327 = (internal_traverse_Tree x_150_224_324) in 
  let val y_155_228_328 = (internal_traverse_Tree x_151_225_325) in 
  let val y_156_229_329 = (internal_traverse_Tree x_152_226_326) in () end end end);

fun mkTree (d_75_213_313) = 
  let val fltIf_260_314 = (d_75_213_313 = 0) in 
  (if fltIf_260_314 then (Leaf (d_75_213_313)) 
   else 
  let val fltAppE_262_315 = (d_75_213_313 - 1) in 
  let val fltPkd_261_316 = (mkTree fltAppE_262_315) in 
  let val fltAppE_264_317 = (d_75_213_313 - 1) in 
  let val fltPkd_263_318 = (mkTree fltAppE_264_317) in 
  let val fltAppE_266_319 = (d_75_213_313 - 1) in 
  let val fltPkd_265_320 = (mkTree fltAppE_266_319) in (Node (1 , fltPkd_261_316, fltPkd_263_318, fltPkd_265_320)) end end end end end end) end;

fun sumTree (tr_69_207_302) = (case tr_69_207_302 of Leaf (n_70_208_303) => n_70_208_303 
  | Node (i_71_209_304 , l_72_210_305, r_73_211_306, ll_74_212_307) => 
  let val fltPrm_257_308 = (sumTree l_72_210_305) in 
  let val fltPrm_256_309 = (i_71_209_304 + fltPrm_257_308) in 
  let val fltPrm_258_310 = (sumTree r_73_211_306) in 
  let val fltPrm_255_311 = (fltPrm_256_309 + fltPrm_258_310) in 
  let val fltPrm_259_312 = (sumTree ll_74_212_307) in (fltPrm_255_311 + fltPrm_259_312) end end end end end);

fun internal_copy_Tree (arg_135_196_291) = (case arg_135_196_291 of Leaf (x_136_197_292) => (Leaf (x_136_197_292)) 
  | Node (x_138_199_294 , x_139_200_295, x_140_201_296, x_141_202_297) => 
  let val y_143_204_299 = (internal_copy_Tree x_139_200_295) in 
  let val y_144_205_300 = (internal_copy_Tree x_140_201_296) in 
  let val y_145_206_301 = (internal_copy_Tree x_141_202_297) in (Node (x_138_199_294 , y_143_204_299, y_144_205_300, y_145_206_301)) end end end);

fun add1Tree (t_63_190_280) = (case t_63_190_280 of Leaf (x_64_191_281) => 
  let val fltPkd_250_282 = (x_64_191_281 + 1) in (Leaf (fltPkd_250_282)) end 
  | Node (i_65_192_283 , x1_66_193_284, x2_67_194_285, x3_68_195_286) => 
  let val fltPkd_251_287 = (i_65_192_283 + 1) in 
  let val fltPkd_252_288 = (add1Tree x1_66_193_284) in 
  let val fltPkd_253_289 = (add1Tree x2_67_194_285) in 
  let val fltPkd_254_290 = (add1Tree x3_68_195_286) in (Node (fltPkd_251_287 , fltPkd_252_288, fltPkd_253_289, fltPkd_254_290)) end end end end);
val _ = (print(Int.toString(
  let val wildcard__47_50_177_267 = (printsym "Running program Ternary Heap: ") in 
  let val wildcard__45_51_178_268 = (printsym "NEWLINE") in 
  let val tree_52_179_269 = (mkTree 15) in 
  let val wildcard__42_53_180_270 = (printsym "Running pass add 1 tree (map, uses=5): ") in 
  let val wildcard__40_54_181_271 = (printsym "NEWLINE") in 
  let val tree__55_182_272 = (add1Tree tree_52_179_269) in 
  let val wildcard__36_56_183_273 = (printsym "End") in 
  let val wildcard__34_57_184_274 = (printsym "NEWLINE") in 
  let val wildcard__32_58_185_275 = (printsym "Running pass sum tree (fold, uses=5): ") in 
  let val wildcard__30_59_186_276 = (printsym "NEWLINE") in 
  let val sum_60_187_277 = (sumTree tree__55_182_272) in 
  let val wildcard__26_61_188_278 = (printsym "End") in 
  let val wildcard__24_62_189_279 = (printsym "NEWLINE") in sum_60_187_277 end end end end end end end end end end end end end)));
val _ = print "\n"
