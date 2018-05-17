infinite.exe:
	@gcc -g -std=gnu11 -Wno-incompatible-pointer-types infinite.c -o infinite.exe

infinite2.exe:
	@gcc -g -std=gnu11 -Wno-incompatible-pointer-types infinite2.c -o infinite2.exe

buildtree.exe:
	@gcc -g -std=gnu11 -Wno-incompatible-pointer-types buildtree.c -o buildtree.exe

all: buildtree.exe infinite.exe

clean:
	@rm -rf *.exe

.PHONY: infinite.exe infinite2.exe buildtree.exe
