# ======================================================================
# Arguments:
# ~~~~~~~~~~~~
#
# MODE      = release | debug
# VERBOSITY = 1 | 2 | 3
# GC        = gen | nongen
#
# Toggles:
# ~~~~~~~~~~~~~
#
# GCSTATS
# POINTER
# PARALLEL
# BUMPALLOC
# ======================================================================

CC        := gcc
AR        := gcc-ar
CFLAGS    := -Wall -Wextra -Wpedantic -Wshadow -std=gnu11 -O3 -flto
RSC       := cargo
RSFLAGS   := -p gibbon-rts-ng
VERBOSITY := 1
MODE      := release

CFLAGS += $(USER_CFLAGS) -D_GIBBON_VERBOSITY=$(VERBOSITY)

ifeq ($(MODE), debug)
	CFLAGS += -O0 -g -D_GIBBON_DEBUG
	RSFLAGS += --features=verbose_evac
else
	RSFLAGS += --release
endif

ifeq ($(GC), nongen)
	CFLAGS += -D_GIBBON_NONGENGC
endif

ifdef $(GCSTATS)
	CFLAGS += -D_GIBBON_GCSTATS
	RSFLAGS += --features=gcstats
endif

ifdef $(POINTER)
	CFLAGS += -D_GIBBON_POINTER
endif

ifdef $(PARALLEL)
	CFLAGS += -fcilkplus -D_GIBBON_PARALLEL
endif

ifdef $(BUMPALLOC)
	CFLAGS += -D_GIBBON_BUMPALLOC_LISTS
endif

# Assume current directory if not set.
GIBBONDIR         ?= ./
GIBBON_NEWRTS_DIR ?= $(GIBBONDIR)/gibbon-rts
RUST_RTS_DIR      := $(GIBBON_NEWRTS_DIR)
C_RTS_DIR         := $(GIBBON_NEWRTS_DIR)/rts-c
LIB_DIR           := $(GIBBON_NEWRTS_DIR)/lib
NAME              := gibbon_rts
RUST_RTS_SO       := libgibbon_rts_ng.so

RUST_RTS_PATH := $(RUST_RTS_DIR)/target/$(MODE)/$(RUST_RTS_SO)

all: c_rts rs_rts

c_rts: $(LIB_DIR)/lib$(NAME).a $(LIB_DIR)/$(NAME).o $(LIB_DIR)/$(NAME).h

rs_rts: $(LIB_DIR)/$(RUST_RTS_SO)

$(LIB_DIR)/$(RUST_RTS_SO): $(RUST_RTS_PATH)
	mkdir -p $(LIB_DIR) && \
	mv $^ $@

$(RUST_RTS_PATH): $(shell find $(RUST_RTS_DIR) -type f -name *.rs)
	cd  $(RUST_RTS_DIR) && \
	$(RSC) build -p gibbon-rts-ng $(RSFLAGS)

$(LIB_DIR)/lib%.a: $(LIB_DIR)/%.o
	$(AR) crs $@ $^

$(LIB_DIR)/%.o: $(C_RTS_DIR)/%.o
	mkdir -p $(LIB_DIR) && \
	mv $^ $@

$(C_RTS_DIR)/%.o: $(C_RTS_DIR)/%.c
	$(CC) $(CFLAGS) -c -o $@ $^

$(LIB_DIR)/%.h: $(C_RTS_DIR)/%.h
	mkdir -p $(LIB_DIR) && \
	cp $^ $@

$(LIB_DIR):
	mkdir -p $(LIB_DIR)

clean:
	rm -rf $(LIB_DIR)

.PHONY: clean
