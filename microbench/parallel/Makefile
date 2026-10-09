CC := clang

build:
	$(CC) -g -O3 -fopencilk sumfoo_1.c -o sumfoo_1_par.exe
	$(CC) -g -O3 -fopencilk sumfoo_2.c -o sumfoo_2_par.exe
	$(CC) -g -O3 -fopencilk sumfoo_3.c -o sumfoo_3_par.exe
	$(CC) -g -O3 -fopencilk sumfoo_pointer.c -o sumfoo_pointer.exe
	$(CC) -g -O3 sumfoo_seq.c -o sumfoo_seq.exe

clean:
	rm -rf *.o *.exe

.PHONY: build
