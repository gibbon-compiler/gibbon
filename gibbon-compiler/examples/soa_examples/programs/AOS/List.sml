datatype dat_List = Cons of (int  *  dat_List) | Nil ;

fun add1 (lst_105_227_296) = (case lst_105_227_296 of Nil => Nil 
  | Cons (i_106_228_297 , rst_107_229_298) => 
  let val i1_108_230_299 = (i_106_228_297 + 1) in 
  let val fltPkd_235_300 = (add1 rst_107_229_298) in (Cons (i1_108_230_299 , fltPkd_235_300)) end end);

fun length (lst_102_224_292) = (case lst_102_224_292 of Nil => 0 
  | Cons (i_103_225_293 , rst_104_226_294) => 
  let val fltPrm_234_295 = (length rst_104_226_294) in (1 + fltPrm_234_295) end);

fun sumList (lst_97_219_288) = (case lst_97_219_288 of Nil => 0 
  | Cons (i_98_220_289 , rst_99_221_290) => 
  let val sumRst_100_222_291 = (sumList rst_99_221_290) in (i_98_220_289 + sumRst_100_222_291) end);

fun internal_copy_List (arg_149_214_283) = (case arg_149_214_283 of Cons (x_150_215_284 , x_151_216_285) => 
  let val y_153_218_287 = (internal_copy_List x_151_216_285) in (Cons (x_150_215_284 , y_153_218_287)) end 
  | Nil => Nil);

fun mkList (length_95_212_279) = 
  let val fltIf_232_280 = (length_95_212_279 <= 0) in 
  (if fltIf_232_280 then Nil 
   else 
  let val fltAppE_233_281 = (length_95_212_279 - 1) in 
  let val rst_96_213_282 = (mkList fltAppE_233_281) in (Cons (length_95_212_279 , rst_96_213_282)) end end) end;

fun internal_traverse_List (arg_154_208_275) = (case arg_154_208_275 of Cons (x_155_209_276 , x_156_210_277) => 
  let val y_158_211_278 = (internal_traverse_List x_156_210_277) in () end 
  | Nil => ());

fun sumListAcc (lst_91_204_270 , acc_92_205_271) = (case lst_91_204_270 of Nil => acc_92_205_271 
  | Cons (i_93_206_272 , rst_94_207_273) => 
  let val fltAppE_231_274 = (acc_92_205_271 + i_93_206_272) in (sumListAcc(rst_94_207_273 , fltAppE_231_274)) end);

fun internal_print_List (arg_159_193_259) = (case arg_159_193_259 of Cons (x_160_194_260 , x_161_195_261) => 
  let val wildcard_164_196_262 = (print "(Cons") in 
  let val wildcard_167_197_263 = (print " ") in 
  let val y_162_198_264 = (print(Int.toString(x_160_194_260))) in 
  let val wildcard_166_199_265 = (print " ") in 
  let val y_163_200_266 = (internal_print_List x_161_195_261) in 
  let val wildcard_165_201_267 = (print ")") in () end end end end end end 
  | Nil => 
  let val wildcard_168_202_268 = (print "(Nil") in 
  let val wildcard_169_203_269 = (print ")") in () end end);
val _ = (case 
  let val wildcard__65_68_170_236 = (print "Running program List: ") in 
  let val wildcard__63_69_171_237 = (print "NEWLINE") in 
  let val lst_70_172_238 = (mkList 100000000) in 
  let val wildcard__60_71_173_239 = (print "Running pass add1 List (map, uses=2): ") in 
  let val wildcard__58_72_174_240 = (print "NEWLINE") in 
  let val lst__73_175_241 = (add1 lst_70_172_238) in 
  let val wildcard__54_74_176_242 = (print "End") in 
  let val wildcard__52_75_177_243 = (print "NEWLINE") in 
  let val wildcard__50_76_178_244 = (print "Running pass length List (fold, uses=1): ") in 
  let val wildcard__48_77_179_245 = (print "NEWLINE") in 
  let val len_78_180_246 = (length lst_70_172_238) in 
  let val wildcard__44_79_181_247 = (print "End") in 
  let val wildcard__42_80_182_248 = (print "NEWLINE") in 
  let val wildcard__40_81_183_249 = (print "Running pass sumList (fold, uses=2): ") in 
  let val wildcard__38_82_184_250 = (print "NEWLINE") in 
  let val sum_83_185_251 = (sumList lst__73_175_241) in 
  let val wildcard__34_84_186_252 = (print "End") in 
  let val wildcard__32_85_187_253 = (print "NEWLINE") in 
  let val wildcard__30_86_188_254 = (print "Running pass sumList tail recursive (fold, uses=2): ") in 
  let val wildcard__28_87_189_255 = (print "NEWLINE") in 
  let val sum__88_190_256 = (sumListAcc(lst__73_175_241 , 0)) in 
  let val wildcard__24_89_191_257 = (print "End") in 
  let val wildcard__22_90_192_258 = (print "NEWLINE") in (sum_83_185_251 , sum__88_190_256, len_78_180_246) end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print ")" in () end);
val _ = print "\n"
