CLANG=clang
GCC=gcc
GEN_OPT=-O3

compile_clang:
	${CLANG} ${GEN_OPT} aos_inplace.c -o aos_inplace.clang.exe 
	${CLANG} ${GEN_OPT} aos_recursive.c -o aos_recursive.clang.exe	
	${CLANG} ${GEN_OPT} soa_inplace.c -o soa_inplace.clang.exe
	${CLANG} ${GEN_OPT} soa_recursive.c -o soa_recursive.clang.exe 	
	
	${CLANG} ${GEN_OPT}  soa_inplace_optimized.c -o soa_inplace_optimized_O3.clang.exe
	${CLANG} ${GEN_OPT} -fno-vectorize -fno-slp-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_disable_autovec.clang.exe	
	${CLANG} ${GEN_OPT} -march=native -Rpass=loop-vectorize -Rpass-missed=loop-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_enable_arch_rpass_autovec.clang.exe
	${CLANG} ${GEN_OPT} -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_inplace_optimized_O3_manually_vectorized.clang.exe

gen_clang_assembly:
	${CLANG} ${GEN_OPT} -S aos_inplace.c -o aos_inplace.clang.s
	${CLANG} ${GEN_OPT} -S aos_recursive.c -o aos_recursive.clang.s
	${CLANG} ${GEN_OPT} -S soa_inplace.c -o soa_inplace.clang.s
	${CLANG} ${GEN_OPT} -S soa_recursive.c -o soa_recursive.clang.s
	
	${CLANG} ${GEN_OPT} -S soa_inplace_optimized.c -o soa_inplace_optimized_O3.clang.s
	${CLANG} ${GEN_OPT} -S -fno-vectorize -fno-slp-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_disable_autovec.clang.s
	${CLANG} ${GEN_OPT} -S -march=native -Rpass=loop-vectorize -Rpass-missed=loop-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_enable_arch_rpass_autovec.clang.s
	${CLANG} ${GEN_OPT} -S -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_inplace_optimized_O3_manually_vectorized.clang.s


compile_gcc:
	${GCC} ${GEN_OPT} aos_inplace.c -o aos_inplace.gcc.exe 
	${GCC} ${GEN_OPT} aos_recursive.c -o aos_recursive.gcc.exe   
	${GCC} ${GEN_OPT} soa_inplace.c -o soa_inplace.gcc.exe
	${GCC} ${GEN_OPT} soa_recursive.c -o soa_recursive.gcc.exe   
	
	${GCC} ${GEN_OPT} soa_inplace_optimized.c -o soa_inplace_optimized_O3.gcc.exe
	${GCC} ${GEN_OPT} -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_disable_autovec.gcc.exe      
	${GCC} ${GEN_OPT} -march=native -ftree-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_enable_arch_rpass_autovec.gcc.exe
	${GCC} ${GEN_OPT} -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_inplace_optimized_O3_manually_vectorized.gcc.exe

gen_gcc_assembly:
	${GCC} ${GEN_OPT} -S aos_inplace.c -o aos_inplace.gcc.s 
	${GCC} ${GEN_OPT} -S aos_recursive.c -o aos_recursive.gcc.s   
	${GCC} ${GEN_OPT} -S soa_inplace.c -o soa_inplace.gcc.s
	${GCC} ${GEN_OPT} -S soa_recursive.c -o soa_recursive.gcc.s   
	
	${GCC} ${GEN_OPT} -S soa_inplace_optimized.c -o soa_inplace_optimized_O3.gcc.s
	${GCC} ${GEN_OPT} -S -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_disable_autovec.gcc.s      
	${GCC} ${GEN_OPT} -S -march=native -ftree-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_enable_arch_rpass_autovec.gcc.s
	${GCC} ${GEN_OPT} -S -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_inplace_optimized_O3_manually_vectorized.gcc.s



all: compile_clang compile_gcc gen_clang_assembly gen_gcc_assembly


clean:
	rm *.exe *.s  
