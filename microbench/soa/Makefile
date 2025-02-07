CLANG=clang
GCC=gcc
GEN_OPT=-O3 -I/local/scratch/a/singhav/env/include/ -L/local/scratch/a/singhav/env/lib/

compile_clang_aos:
	${CLANG} ${GEN_OPT} aos_iterative_in_place.c -o aos_iterative_in_place.clang.exe -lpapi
	${CLANG} ${GEN_OPT} aos_iterative_out_of_place.c -o aos_iterative_out_of_place.clang.exe -lpapi	
	${CLANG} ${GEN_OPT} aos_recursive_in_place.c -o aos_recursive_in_place.clang.exe -lpapi
	${CLANG} ${GEN_OPT} aos_recursive_out_of_place.c -o aos_recursive_out_of_place.clang.exe -lpapi

compile_clang_soa:
	${CLANG} ${GEN_OPT} soa_iterative_in_place.c -o soa_iterative_in_place.clang.exe -lpapi
	${CLANG} ${GEN_OPT} soa_iterative_out_of_place.c -o soa_iterative_out_of_place.clang.exe -lpapi
	${CLANG} ${GEN_OPT} soa_recursive_in_place.c -o soa_recursive_in_place.clang.exe -lpapi
	${CLANG} ${GEN_OPT} soa_recursive_out_of_place.c -o soa_recursive_out_of_place.clang.exe -lpapi
	${CLANG} ${GEN_OPT} soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3.clang.exe -lpapi
	${CLANG} ${GEN_OPT} soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3.clang.exe -lpapi
	${CLANG} ${GEN_OPT} -fno-vectorize -fno-slp-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_disable_autovec.clang.exe -lpapi
	${CLANG} ${GEN_OPT} -fno-vectorize -fno-slp-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_disable_autovec.clang.exe -lpapi	
	${CLANG} ${GEN_OPT} -march=native -Rpass=loop-vectorize -Rpass-missed=loop-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_enable_arch_rpass_autovec.clang.exe -lpapi
	${CLANG} ${GEN_OPT} -march=native -Rpass=loop-vectorize -Rpass-missed=loop-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_enable_arch_rpass_autovec.clang.exe -lpapi
	${CLANG} ${GEN_OPT} -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_iterative_in_place_optimized_O3_manually_vectorized.clang.exe -lpapi

gen_clang_assembly_aos:
	${CLANG} ${GEN_OPT} -S aos_iterative_in_place.c -o aos_iterative_in_place.clang.s
	${CLANG} ${GEN_OPT} -S aos_iterative_out_of_place.c -o aos_iterative_out_of_place.clang.s        
	${CLANG} ${GEN_OPT} -S aos_recursive_in_place.c -o aos_recursive_in_place.clang.s
	${CLANG} ${GEN_OPT} -S aos_recursive_out_of_place.c -o aos_recursive_out_of_place.clang.s

	
gen_clang_assembly_soa:
	${CLANG} ${GEN_OPT} -S soa_iterative_in_place.c -o soa_iterative_in_place.clang.s
	${CLANG} ${GEN_OPT} -S soa_iterative_out_of_place.c -o soa_iterative_out_of_place.clang.s
	${CLANG} ${GEN_OPT} -S soa_recursive_in_place.c -o soa_recursive_in_place.clang.s
	${CLANG} ${GEN_OPT} -S soa_recursive_out_of_place.c -o soa_recursive_out_of_place.clang.s
	${CLANG} ${GEN_OPT} -S soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3.clang.s
	${CLANG} ${GEN_OPT} -S soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3.clang.s
	${CLANG} ${GEN_OPT} -S -fno-vectorize -fno-slp-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_disable_autovec.clang.s
	${CLANG} ${GEN_OPT} -S -fno-vectorize -fno-slp-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_disable_autovec.clang.s
	${CLANG} ${GEN_OPT} -S -march=native -ftree-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_enable_arch_rpass_autovec.clang.s
	${CLANG} ${GEN_OPT} -S -march=native -ftree-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_enable_arch_rpass_autovec.clang.s
	${CLANG} ${GEN_OPT} -S -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_iterative_in_place_optimized_O3_manually_vectorized.clang.s

compile_gcc_aos:
	${GCC} ${GEN_OPT} aos_iterative_in_place.c -o aos_iterative_in_place.gcc.exe -lpapi
	${GCC} ${GEN_OPT} aos_iterative_out_of_place.c -o aos_iterative_out_of_place.gcc.exe -lpapi        
	${GCC} ${GEN_OPT} aos_recursive_in_place.c -o aos_recursive_in_place.gcc.exe -lpapi
	${GCC} ${GEN_OPT} aos_recursive_out_of_place.c -o aos_recursive_out_of_place.gcc.exe -lpapi
  
	
compile_gcc_soa:
	${GCC} ${GEN_OPT} soa_iterative_in_place.c -o soa_iterative_in_place.gcc.exe -lpapi
	${GCC} ${GEN_OPT} soa_iterative_out_of_place.c -o soa_iterative_out_of_place.gcc.exe -lpapi
	${GCC} ${GEN_OPT} soa_recursive_in_place.c -o soa_recursive_in_place.gcc.exe -lpapi
	${GCC} ${GEN_OPT} soa_recursive_out_of_place.c -o soa_recursive_out_of_place.gcc.exe -lpapi
	${GCC} ${GEN_OPT} soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3.gcc.exe -lpapi
	${GCC} ${GEN_OPT} soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3.gcc.exe -lpapi
	${GCC} ${GEN_OPT} -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_disable_autovec.gcc.exe -lpapi
	${GCC} ${GEN_OPT} -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_disable_autovec.gcc.exe -lpapi
	${GCC} ${GEN_OPT} -march=native -ftree-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_enable_arch_rpass_autovec.gcc.exe -lpapi
	${GCC} ${GEN_OPT} -march=native -ftree-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_enable_arch_rpass_autovec.gcc.exe -lpapi
	${GCC} ${GEN_OPT} -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_iterative_in_place_optimized_O3_manually_vectorized.gcc.exe -lpapi


gen_gcc_assembly_aos:
	${GCC} ${GEN_OPT} -S aos_iterative_in_place.c -o aos_iterative_in_place.gcc.s
	${GCC} ${GEN_OPT} -S aos_iterative_out_of_place.c -o aos_iterative_out_of_place.gcc.s
	${GCC} ${GEN_OPT} -S aos_recursive_in_place.c -o aos_recursive_in_place.gcc.s
	${GCC} ${GEN_OPT} -S aos_recursive_out_of_place.c -o aos_recursive_out_of_place.gcc.s   
	
gen_gcc_assembly_soa:
	${GCC} ${GEN_OPT} -S soa_iterative_in_place.c -o soa_iterative_in_place.gcc.s
	${GCC} ${GEN_OPT} -S soa_iterative_out_of_place.c -o soa_iterative_out_of_place.gcc.s
	${GCC} ${GEN_OPT} -S soa_recursive_in_place.c -o soa_recursive_in_place.gcc.s
	${GCC} ${GEN_OPT} -S soa_recursive_out_of_place.c -o soa_recursive_out_of_place.gcc.s
	${GCC} ${GEN_OPT} -S soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3.gcc.s
	${GCC} ${GEN_OPT} -S soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3.gcc.s
	${GCC} ${GEN_OPT} -S -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_disable_autovec.gcc.s
	${GCC} ${GEN_OPT} -S -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_disable_autovec.gcc.s
	${GCC} ${GEN_OPT} -S -march=native -ftree-vectorize soa_iterative_optimized_in_place.c -o soa_iterative_in_place_optimized_O3_enable_arch_rpass_autovec.gcc.s
	${GCC} ${GEN_OPT} -S -march=native -ftree-vectorize soa_iterative_optimized_out_of_place.c -o soa_iterative_out_of_place_optimized_O3_enable_arch_rpass_autovec.gcc.s
	${GCC} ${GEN_OPT} -S -march=native -mavx2 soa_inplace_optimized_manually_vectorized.c -o soa_iterative_in_place_optimized_O3_manually_vectorized.gcc.s


all: compile_clang_aos compile_clang_soa compile_gcc_aos compile_gcc_soa gen_clang_assembly_aos gen_clang_assembly_soa gen_gcc_assembly_aos gen_gcc_assembly_soa


clean:
	rm *.exe *.s  
