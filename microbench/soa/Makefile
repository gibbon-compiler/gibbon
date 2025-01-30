CLANG=clang
GCC=gcc
GEN_OPT=-O3

compile_clang:
	${CLANG} ${GEN_OPT} aos_inplace.c -o aos_inplace.clang.exe 
	${CLANG} ${GEN_OPT} aos_recursive.c -o aos_recursive.clang.exe	
	${CLANG} ${GEN_OPT} soa_inplace.c -o soa_inplace.clang.exe
	${CLANG} ${GEN_OPT} soa_recursive.c -o soa_recursive.clang.exe 	
	
	${CLANG} ${GEN_OPT} soa_inplace_optimized.c -o soa_inplace_optimized_O3.clang.exe
	${CLANG} ${GEN_OPT} -fno-vectorize -fno-slp-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_disable_autovec.clang.exe	
	${CLANG} ${GEN_OPT} -march=native -Rpass=loop-vectorize -Rpass-missed=loop-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_enable_arch_rpass_autovec.clang.exe
	${CLANG} ${GEN_OPT} -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_inplace_optimized_O3_manually_vectorized.clang.exe

compile_gcc:
	${GCC} ${GEN_OPT} aos_inplace.c -o aos_inplace.gcc.exe 
	${GCC} ${GEN_OPT} aos_recursive.c -o aos_recursive.gcc.exe   
	${GCC} ${GEN_OPT} soa_inplace.c -o soa_inplace.gcc.exe
	${GCC} ${GEN_OPT} soa_recursive.c -o soa_recursive.gcc.exe   
	
	${GCC} ${GEN_OPT} soa_inplace_optimized.c -o soa_inplace_optimized_O3.gcc.exe
	${GCC} ${GEN_OPT} -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_disable_autovec.gcc.exe      
	${GCC} ${GEN_OPT} -march=native -ftree-vectorize soa_inplace_optimized.c -o soa_inplace_optimized_O3_enable_arch_rpass_autovec.gcc.exe
	${GCC} ${GEN_OPT} -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_inplace_optimized_O3_manually_vectorized.gcc.exe

all: compile_clang compile_gcc


clean:
	rm *.exe 
