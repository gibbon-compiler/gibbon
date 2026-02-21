datatype dat_Tree = Leaf of (int) | Node of ( dat_Tree  *  dat_Tree) ;

fun internal_print_Tree (arg_154_216_301) = (case arg_154_216_301 of Leaf (x_155_217_302) => 
  let val wildcard_157_218_303 = (print "(Leaf") in 
  let val wildcard_159_219_304 = (print " ") in 
  let val y_156_220_305 = (print(Int.toString(x_155_217_302))) in 
  let val wildcard_158_221_306 = (print ")") in () end end end end 
  | Node (x_160_222_307 , x_161_223_308) => 
  let val wildcard_164_224_309 = (print "(Node") in 
  let val wildcard_167_225_310 = (print " ") in 
  let val y_162_226_311 = (internal_print_Tree x_160_222_307) in 
  let val wildcard_166_227_312 = (print " ") in 
  let val y_163_228_313 = (internal_print_Tree x_161_223_308) in 
  let val wildcard_165_229_314 = (print ")") in () end end end end end end);

fun internal_traverse_Tree (arg_147_210_295) = (case arg_147_210_295 of Leaf (x_148_211_296) => () 
  | Node (x_150_212_297 , x_151_213_298) => 
  let val y_152_214_299 = (internal_traverse_Tree x_150_212_297) in 
  let val y_153_215_300 = (internal_traverse_Tree x_151_213_298) in () end end);

fun mkTree (d_89_207_286 , acc_90_208_287) = 
  let val fltIf_235_288 = (d_89_207_286 = 0) in 
  (if fltIf_235_288 then (Leaf (acc_90_208_287)) 
   else 
  let val fltAppE_237_289 = (d_89_207_286 - 1) in 
  let val fltAppE_238_290 = (d_89_207_286 + acc_90_208_287) in 
  let val fltPkd_236_291 = (mkTree(fltAppE_237_289 , fltAppE_238_290)) in 
  let val fltAppE_240_292 = (d_89_207_286 - 1) in 
  let val fltAppE_241_293 = (d_89_207_286 + acc_90_208_287) in 
  let val fltPkd_239_294 = (mkTree(fltAppE_240_292 , fltAppE_241_293)) in (Node (fltPkd_236_291 , fltPkd_239_294)) end end end end end end) end;

fun sumTree (tr_85_203_280) = (case tr_85_203_280 of Leaf (n_86_204_281) => n_86_204_281 
  | Node (l_87_205_282 , r_88_206_283) => 
  let val fltPrm_233_284 = (sumTree l_87_205_282) in 
  let val fltPrm_234_285 = (sumTree r_88_206_283) in (fltPrm_233_284 + fltPrm_234_285) end end);

fun internal_copy_Tree (arg_140_196_273) = (case arg_140_196_273 of Leaf (x_141_197_274) => (Leaf (x_141_197_274)) 
  | Node (x_143_199_276 , x_144_200_277) => 
  let val y_145_201_278 = (internal_copy_Tree x_143_199_276) in 
  let val y_146_202_279 = (internal_copy_Tree x_144_200_277) in (Node (y_145_201_278 , y_146_202_279)) end end);

fun add1Tree (t_81_192_266) = (case t_81_192_266 of Leaf (x_82_193_267) => 
  let val fltPkd_230_268 = (x_82_193_267 + 1) in (Leaf (fltPkd_230_268)) end 
  | Node (x1_83_194_269 , x2_84_195_270) => 
  let val fltPkd_231_271 = (add1Tree x1_83_194_269) in 
  let val fltPkd_232_272 = (add1Tree x2_84_195_270) in (Node (fltPkd_231_271 , fltPkd_232_272)) end end);

fun sumTreeAcc (t_75_186_260 , acc_76_187_261) = (case t_75_186_260 of Leaf (n_77_188_262) => (acc_76_187_261 + n_77_188_262) 
  | Node (l_78_189_263 , r_79_190_264) => 
  let val acc1_80_191_265 = (sumTreeAcc(l_78_189_263 , acc_76_187_261)) in (sumTreeAcc(r_79_190_264 , acc1_80_191_265)) end);
val _ = (case 
  let val wildcard__54_57_168_242 = (print "Running program MonoTree: ") in 
  let val wildcard__52_58_169_243 = (print "NEWLINE") in 
  let val tree_59_170_244 = (mkTree(23 , 0)) in 
  let val wildcard__49_60_171_245 = (print "Running pass add1Tree (map, uses=3): ") in 
  let val wildcard__47_61_172_246 = (print "NEWLINE") in 
  let val tree__62_173_247 = (add1Tree tree_59_170_244) in 
  let val wildcard__43_63_174_248 = (print "End") in 
  let val wildcard__41_64_175_249 = (print "NEWLINE") in 
  let val wildcard__39_65_176_250 = (print "Running pass sumTree (fold, uses=3): ") in 
  let val wildcard__37_66_177_251 = (print "NEWLINE") in 
  let val val_67_178_252 = (sumTree tree__62_173_247) in 
  let val wildcard__33_68_179_253 = (print "End") in 
  let val wildcard__31_69_180_254 = (print "NEWLINE") in 
  let val wildcard__29_70_181_255 = (print "Running pass sumTree TailRec (fold, uses=3): ") in 
  let val wildcard__27_71_182_256 = (print "NEWLINE") in 
  let val val__72_183_257 = (sumTreeAcc(tree__62_173_247 , 0)) in 
  let val wildcard__23_73_184_258 = (print "End") in 
  let val wildcard__21_74_185_259 = (print "NEWLINE") in (val_67_178_252 , val__72_183_257) end end end end end end end end end end end end end end end end end end of (x__1 , x__2) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print ")" in () end);
val _ = print "\n"
