build:
	gcc-7 -g -O3 -fcilkplus sumfoo_1.c -o sumfoo_1_par.exe
	gcc-7 -g -O3 -fcilkplus sumfoo_2.c -o sumfoo_2_par.exe
	gcc-7 -g -O3 -fcilkplus sumfoo_3.c -o sumfoo_3_par.exe
	gcc-7 -g -O3 sumfoo_seq.c -o sumfoo_seq.exe

clean:
	rm -rf *.o *.exe

.PHONY: build
