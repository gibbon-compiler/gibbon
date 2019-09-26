build:
	gcc-7 -g -O3 -fcilkplus sumtree.c -o sumtree.exe
	gcc-7 -g -O3 -fcilkplus -DPARALLEL sumtree.c -o sumtree_par.exe

clean:
	rm -rf *.o *.exe

.PHONY: build
