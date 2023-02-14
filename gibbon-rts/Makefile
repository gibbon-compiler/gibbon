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
CFLAGS    := -Wall -Wextra -Wpedantic -Wshadow -std=gnu11 -flto
RSC       := cargo
RSFLAGS   := -v
VERBOSITY := 1
MODE      := release

CFLAGS += $(USER_CFLAGS) -D_GIBBON_VERBOSITY=$(VERBOSITY)

ifeq ($(MODE), debug)
	CFLAGS += -O0 -g -D_GIBBON_DEBUG
else
	CFLAGSS += -O3
	RSFLAGS += --release
endif

ifeq ($(shell test $(VERBOSITY) -gt 2; echo $$?),0)
	RSFLAGS += --features=verbose_evac
endif

ifeq ($(GC), nongen)
	CFLAGS += -D_GIBBON_NONGENGC
endif

ifeq ($(GCSTATS), 1)
	CFLAGS += -D_GIBBON_GCSTATS
	RSFLAGS += --features=gcstats
endif

ifeq ($(PRINT_GCSTATS), 1)
	CFLAGS += -D_GIBBON_PRINT_GCSTATS
endif

ifeq ($(POINTER), 1)
	CFLAGS += -D_GIBBON_POINTER
endif

ifeq ($(PARALLEL), 1)
	CFLAGS += -fcilkplus -D_GIBBON_PARALLEL
endif

ifeq ($(BUMPALLOC), 1)
	CFLAGS += -D_GIBBON_BUMPALLOC_LISTS -D_GIBBON_BUMPALLOC_HEAP
endif

ifeq ($(DISABLE_EAGER_PROMOTION), 1)
	CFLAGS += -D_GIBBON_DISABLE_EAGER_PROMOTION
	RSFLAGS += --features=disable_eager_promotion
endif

ifeq ($(NOBURN), 1)
	RSFLAGS += --features=noburn
endif

ifeq ($(NOCOMPACT), 1)
	RSFLAGS += --features=nocompact
endif

# Assume current directory if not set.
GIBBONDIR         ?= ./
RUST_RTS_DIR      := $(GIBBONDIR)/gibbon-rts
C_RTS_DIR         := $(RUST_RTS_DIR)/rts-c
BUILD_DIR         := $(RUST_RTS_DIR)/build
NAME              := gibbon_rts
RUST_RTS_SO       := libgibbon_rts_ng.so
RUST_RTS_PATH     := $(RUST_RTS_DIR)/target/$(MODE)/$(RUST_RTS_SO)
RUST_SOURCES      := $(shell find $(RUST_RTS_DIR) -type f -name *.rs)


all: rts

rts: c_rts rs_rts

c_rts: $(BUILD_DIR)/lib$(NAME).a $(BUILD_DIR)/$(NAME).o $(BUILD_DIR)/$(NAME).h

rs_rts: $(BUILD_DIR)/$(RUST_RTS_SO)

test: t_rs_rts

t_rs_rts: $(RUST_SOURCES)
	cd  $(RUST_RTS_DIR) && \
	$(RSC) test -- --nocapture

$(BUILD_DIR)/$(RUST_RTS_SO): $(RUST_RTS_PATH)
	mkdir -p $(BUILD_DIR) && \
	mv $^ $@

$(RUST_RTS_PATH): $(RUST_SOURCES)
	cd  $(RUST_RTS_DIR) && \
	$(RSC) build -p gibbon-rts-ng $(RSFLAGS)

$(BUILD_DIR)/lib%.a: $(BUILD_DIR)/%.o
	$(AR) crs $@ $^

$(BUILD_DIR)/%.o: $(C_RTS_DIR)/%.o
	mkdir -p $(BUILD_DIR) && \
	mv $^ $@

$(C_RTS_DIR)/%.o: $(C_RTS_DIR)/%.c
	$(CC) $(CFLAGS) -c -o $@ $^

$(BUILD_DIR)/%.h: $(C_RTS_DIR)/%.h
	mkdir -p $(BUILD_DIR) && \
	ln -s $^ $@

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

clean:
	rm -rf $(BUILD_DIR) $(RUST_RTS_DIR)/target

.PHONY: clean
