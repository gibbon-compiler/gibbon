
default: binary_racket cleaned_racket sorted_binary_files.txt sorted_cleaned_files.txt

# We don't check in input data sets to git. We fetch them.

# 1.0: initial cut from Racket main distro
# 1.1: remove files containing '#<'.  Also fix tarball to include expanded_racket subdir.
# 1.2: larger dataset, from Racket 6.6 main distro.
DATASET=racket_expanded_files_v1.2.tgz

fetch: ${DATASET}

$(DATASET):
	wget http://cs.indiana.edu/~rrnewton/files/${DATASET}

# Updated to no-list version, v1.6 [2016.11.04]:
wget_cleaned:
	wget http://cs.indiana.edu/~rrnewton/files/racket_cleaned_asts_v1.6.tgz
	tar xf racket_cleaned_asts_v1.6.tgz

# Updated to version with .gpkd file exts, v1.7 [2017.01.09]
wget_binary:
	wget http://cs.indiana.edu/~rrnewton/files/racket_binary_packed_asts_v1.7.tgz
	tar xf racket_binary_packed_asts_v1.7.tgz

wget_mega:
	wget http://cs.indiana.edu/~rrnewton/files/mega_asts_1.0.tbz
	tar xvf mega_asts_1.0.tbz

expanded_racket: ${DATASET}
	mkdir -p $@
	cd $@; time tar xf ../${DATASET}
	echo "\nEliminating files with offending character sequences:"
	grep -risl '#<' ./expanded_racket/ > offenders.txt
	echo "Number of offenders: "`wc -l offenders.txt`
	du -sh $@
	for file in `cat offenders.txt`; do rm $$file; done
	du -sh $@
	find $@ -size 0 > offenders_empty.txt
	for file in `cat offenders_empty.txt`; do rm $$file; done
	echo "\nOffenders and zero-sized removed.  Done."
	$(MAKE) largest

cleaned_racket:
	$(MAKE) wget_cleaned

rebuild_cleaned_racket: rewrite.rkt
	mkdir -p $@
	cd expanded_racket; \
         for f in `find -name "*.sexp"`; do \
          mkdir -p `dirname "../cleaned_racket/$$f"`; \
	  echo "$$f" "../cleaned_racket/$$f"; \
         done | racket ../rewrite.rkt;
	$(MAKE) largest_clean



# [2017.01.12] Make the default fetching it
binary_racket:
	$(MAKE) wget_binary

rebuild_binary_racket: 
	mkdir -p $@
	rm -f ./conversion_list.txt
	cd cleaned_racket; \
          for f in `find -name "*.sexp"`; do \
            mkdir -p `dirname "../binary_racket/$$f"`; \
            echo "$$f" ../binary_racket/`dirname $$f`/`basename $$f .sexp`.gpkd >> ../conversion_list.txt; \
          done
	cd cleaned_racket; \
         cat ../conversion_list.txt | racket ../binary_pack.rkt;

# --------------------------------------------------------------------------------

# Build a list of all files from biggest to smallest:
sorted_binary_files.txt:
	cd binary_racket; find ./ -name "*.gpkd" -type f -printf "%s %p\n" | sort -n -r > ../$@

sorted_cleaned_files.txt:
	cd cleaned_racket; find ./ -name "*.sexp" -type f -printf "%s %p\n" | sort -n -r > ../$@

# Debugging cruft:
sorted_success.txt:
	rm -f debug/sized_succeeded.txt 
	for file in `cat debug/packed_succeeded.txt`; do \
          echo `stat -c %s ./binary_racket/$$file` $$file; done > debug/sized_succeeded.txt
	cat debug/sized_succeeded.txt | sort -n -r > $@

# Default:
MEGASIZE=10

mega_asts:
	$(MAKE) wget_mega

# These are larger and larger prefixes of the list of 4456 Racket files.
megas:
	$(MAKE) MEGASIZE=1 mega
	$(MAKE) MEGASIZE=5 mega
	$(MAKE) MEGASIZE=10 mega
	$(MAKE) MEGASIZE=50 mega
	$(MAKE) MEGASIZE=100 mega
	$(MAKE) MEGASIZE=500 mega
	$(MAKE) MEGASIZE=4456 mega

mega: mega_asts/mega_$(MEGASIZE).gpkd

# These are instead more artifical/balanced replications of a single file.
mega1s: 
	$(MAKE) REPLICATE=1 mega1
	$(MAKE) REPLICATE=5 mega1
	$(MAKE) REPLICATE=10 mega1
	$(MAKE) REPLICATE=50 mega1
	$(MAKE) REPLICATE=100 mega1
	$(MAKE) REPLICATE=500 mega1
	$(MAKE) REPLICATE=4456 mega1

mega1: mega_asts/mega1_$(REPLICATE).gpkd

mega_asts/mega_$(MEGASIZE).sexp: cleaned_racket sorted_cleaned_files.txt
	mkdir -p ./mega_asts
	head -n$(MEGASIZE) sorted_cleaned_files.txt | awk '{ print "./cleaned_racket/"$$2 }' > $@.list
	cat $@.list | racket combine.rkt --out $@

mega_asts/mega_$(MEGASIZE).gpkd: mega_asts/mega_$(MEGASIZE).sexp
	raco make binary_pack.rkt
	echo $< $@ | racket binary_pack.rkt

mega_asts/mega1_$(REPLICATE).sexp: mega_asts/mega_1.sexp
	( cat `yes ./mega_asts/mega_1.sexp.list | head -$(REPLICATE) | paste -s` )> mega_asts/mega1_$(REPLICATE).sexp.list
	cat mega_asts/mega1_$(REPLICATE).sexp.list | racket combine.rkt --out mega_asts/mega1_$(REPLICATE).sexp

# mega_asts/mega1_$(REPLICATE).gpkd: mega_asts/mega1_$(REPLICATE).sexp
mega_asts/*.gpkd: mega_asts/*.sexp
	raco make binary_pack.rkt
	echo $< $@ | racket binary_pack.rkt

pack_all:
	raco make binary_pack.rkt
	for f in mega_asts/nested*.sexp; do \
	  echo $$f "$${f%.sexp}.gpkd" | racket binary_pack.rkt ; done

# These nested versions create a deeper tree by calling combine.rkt log(n) times.
nested:
	$(MAKE) mega_asts/nested_1.sexp
	$(MAKE) COUNT=2 go_nested
	$(MAKE) COUNT=4 go_nested
	$(MAKE) COUNT=8 go_nested
	$(MAKE) COUNT=16 go_nested
	$(MAKE) COUNT=32 go_nested
	$(MAKE) COUNT=64 go_nested
	$(MAKE) COUNT=128 go_nested
	$(MAKE) COUNT=256 go_nested
	$(MAKE) COUNT=512 go_nested

go_nested: mega_asts/nested_$(COUNT).sexp
mega_asts/nested_1.sexp: mega_asts/mega_1.sexp
	cp $^ $@

COUNT_HALF = $(shell expr $(COUNT) / 2)
mega_asts/nested_$(COUNT).sexp: mega_asts/nested_$(COUNT_HALF).sexp
	racket combine.rkt --out $@ $^ $^

largest:
	echo "Here are some of the larger files:"
	find expanded_racket/ -type f -printf "%s\t%p\n" | sort -n | tail

largest_clean:
	echo "Here are some of the larger, cleaned files:"
	find cleaned_racket -type f -printf "%s\t%p\n" | sort -n | tail


clean:
	rm -f sorted_binary_files.txt sorted_cleaned_files.txt
	rm -rf racket_cleaned*.tgz racket_binary*.tgz

distclean: clean
	rm -rf ./expanded_racket ./cleaned_racket ./binary_racket 
	rm -rf mega_asts

.PHONY: default fetch largest rebuild_binary_racket mega
