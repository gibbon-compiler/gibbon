# ======================================================================
# This Makefile ties together different pieces and builds the parts of
# the software that are NOT built by Haskell's stack tool (i.e. like
# ./gibbon-compiler is).
# ======================================================================

all: racket subst

# [2017.01.11] Not building this by default for now. Not using it (yet):
deps:
	cd deps/sexpr-1.3 && ./configure && $(MAKE)

racket: gibbon-lang

SANDBOX=.racket_sandbox

gibbon-lang: $(SANDBOX)
	rm -rf $(SANDBOX)/*
	PLTADDONDIR=`pwd`/$(SANDBOX) raco pkg install --link ./gibbon

# OLD WAY: user-wide install.  No good for testing.
# RRN [2016.12.28] was there a single command that is idempotent?
#	raco pkg install --link ./gibbon || raco pkg update --link ./gibbon

$(SANDBOX):
	mkdir -p $@

# -------------------------- NIX ----------------------------------
# Bring up a shell using a fixed, known-good software image.
#  - 51a83266d164195698f04468d90d2c6238ed3491 is a snapshot of nixos-17.03 channel on [2017.08.16]
#  - 09b9f7e7c496813f3ecd01c39a976ae3637e41e6 is a snapshot of nixos-17.03 on [2017.10.03]
shell: nix-shell
nix-shell:
	nix-shell -I nixpkgs=`cat .nix_default_environment.txt`

pure:
	nix-shell --pure -I nixpkgs=`cat .nix_default_environment.txt`

# Just bring up a quick-and-dirty Nix shell with the user's nixpkgs
# environment.  This should, in practice, be pretty safe as stack
# controls all the Haskell versioning, and stack should be pretty darn
# backwards compatible.
head: head-shell
head-shell:
	nix-shell --arg pkgs 'import <nixpkgs> {}'
# -------------------------- /NIX ----------------------------------


# Aggressive clean of the working copy:
clean:
	rm -rf $(SANDBOX) 
	find -name .stack-work | xargs rm -rf
	cd ./gibbon-compiler/; stack clean
	find -name compiled     | xargs rm -rf
	cd ./gibbon-compiler/examples/; make distclean

.PHONY: subst deps all racket gibbon-lang shell nix-shell pure head head-shell
