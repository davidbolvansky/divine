GENERATOR != if ninja --version > /dev/null 2>&1 || \
                ninja-build --version > /dev/null 2>&1; then echo Ninja; else echo Unix Makefiles; fi
# fallback
GENERATOR ?= Unix Makefiles

-include /etc/divine.make # for system-wide config
-include local.make

CMAKE ?= cmake
CC ?= cc
CXX ?= c++
DEFAULT_FLAVOUR ?= release
PREFIX ?= /opt/divine

MAKEFLAGS ?= --no-print-directory
OBJ ?= $(PWD)/_build.
BENCH_NAME ?= $(LOGNAME)
EXTRA != if test "$(GENERATOR)" = Ninja && test -n "$(VERBOSE)"; then echo -v -d explain; fi; \
         if test -n "$(JOBS)"; then echo -j $(JOBS); fi

TOOLDIR = $(OBJ)toolchain
CLANG = $(TOOLDIR)/clang/
RTBIN = $(TOOLDIR)/runtime
RTSRC = $(PWD)/runtime

LIBUNWIND_LDIR = $(RTBIN)/libunwind/src
CXX_LDIR = $(TOOLDIR)/lib
CXX_STATIC = $(TOOLDIR)/lib-static

LDFLAGS_ = -L$(LIBUNWIND_LDIR) -Wl,-rpath,$(LIBUNWIND_LDIR) \
           -L$(CXX_LDIR) -Wl,-rpath,$(CXX_LDIR)
BUILD_RPATH = $(LIBUNWIND_LDIR):$(CXX_LDIR)

CXXFLAGS_ = -isystem $(RTSRC)/libcxxabi/include -isystem $(RTSRC)/libcxx/include \
            -isystem $(RTSRC)/libunwind/include \
            -stdlib=libc++ -nostdinc++ -Wno-unused-command-line-argument

TOOLCHAIN_ = CMAKE_C_COMPILER=$(CLANG)/bin/clang;CMAKE_CXX_COMPILER=$(CLANG)/bin/clang++;\
	     CMAKE_CXX_FLAGS=$(CXXFLAGS_)
TOOLCHAIN  ?= $(TOOLCHAIN_);CMAKE_EXE_LINKER_FLAGS=$(LDFLAGS_);CMAKE_SHARED_LINKER_FLAGS=$(LDFLAGS_)
TOOLSTAMP  ?= $(TOOLDIR)/stamp-v2

CONFIG        += CMAKE_INSTALL_PREFIX=${PREFIX};BUILD_SHARED_LIBS=ON
static_FLAGS  += CMAKE_BUILD_TYPE=Release;$(TOOLCHAIN);$(CONFIG);BUILD_SHARED_LIBS=OFF;STATIC_BUILD=ON
bench_FLAGS   += CMAKE_BUILD_TYPE=Release;BUILD_SHARED_LIBS=OFF;\
		 CMAKE_EXE_LINKER_FLAGS=-L$(CXX_STATIC) $(LDFLAGS_);$(TOOLCHAIN)
release_FLAGS += CMAKE_BUILD_TYPE=RelWithDebInfo;$(TOOLCHAIN);$(CONFIG)
semidbg_FLAGS += CMAKE_BUILD_TYPE=SemiDbg;$(TOOLCHAIN);$(CONFIG)
debug_FLAGS   += CMAKE_BUILD_TYPE=Debug;$(TOOLCHAIN);$(CONFIG)

asan_CXXFLAGS += -fsanitize=address -fno-omit-frame-pointer -fno-optimize-sibling-calls -g -O1
asan_FLAGS = $(debug_FLAGS);CMAKE_CXX_FLAGS_DEBUG=$(asan_CXXFLAGS)

toolchain_FLAGS += CMAKE_BUILD_TYPE=RelWithDebInfo;TOOLCHAIN=ON; \
		   CMAKE_CXX_COMPILER=$(CXX);CMAKE_C_COMPILER=$(CC); \
		   CMAKE_INSTALL_PREFIX;${PREFIX}

all: $(DEFAULT_FLAVOUR)

FLAVOURS = debug asan release semidbg static bench
TARGETS = divine unit functional website check llvm-utils clang test-divine \
          install lart runner divbench divcheck divcc
DEFTARGETS = divine unit functional website check install lart divcheck divcc

${DEFTARGETS}:
	$(MAKE) $(DEFAULT_FLAVOUR)-$@

${FLAVOURS}:
	$(MAKE) $@-divine

divbench:
	$(MAKE) bench-divbench
	@echo your binary is at $(OBJ)bench/tools/divbench

divbench-install:
	test -d $(BENCH_DIR)
	$(MAKE) divbench
	cp $(OBJ)bench/tools/divbench $(BENCH_DIR)/$(BENCH_NAME).`date +%Y-%m-%d.%H%M`

SETENV = env BUILD_RPATH=$(BUILD_RPATH) TESTHOOK="$(TESTHOOK)"

config:
	@if test -z "$(FLAVOUR)"; then echo "ERROR: FLAVOUR must be provided"; false; fi
	mkdir -p $(OBJ)$(FLAVOUR)
	echo "$($(FLAVOUR)_FLAGS)" > $(OBJ)$(FLAVOUR)/config.tmp
	$(CMAKE) -E copy_if_different $(OBJ)$(FLAVOUR)/config.tmp $(OBJ)$(FLAVOUR)/config.vars
	if ! test -e $(OBJ)$(FLAVOUR)/config.done; then  \
	  chmod +x test/divine; \
	  cd $(OBJ)$(FLAVOUR) && $(CMAKE) $(PWD) $(CMAKE_EXTRA) -G "$(GENERATOR)"; \
	  touch $(OBJ)$(FLAVOUR)/config.done; fi

build: config
	$(SETENV) $(CMAKE) --build $(OBJ)$(FLAVOUR) --target $(TARGET) -- $(EXTRA)

${TARGETS:%=static-%}: $(TOOLSTAMP)
	$(MAKE) build FLAVOUR=static TARGET=${@:static-%=%}

${TARGETS:%=debug-%}: $(TOOLSTAMP)
	$(MAKE) build FLAVOUR=debug TARGET=${@:debug-%=%}

${TARGETS:%=semidbg-%}: $(TOOLSTAMP)
	$(MAKE) build FLAVOUR=semidbg TARGET=${@:semidbg-%=%}

${TARGETS:%=release-%}: $(TOOLSTAMP)
	$(MAKE) build FLAVOUR=release TARGET=${@:release-%=%}

${TARGETS:%=bench-%}: $(TOOLSTAMP)
	$(MAKE) build FLAVOUR=bench TARGET=${@:bench-%=%}

${TARGETS:%=asan-%}:
	$(MAKE) build FLAVOUR=asan TARGET=${@:asan-%=%}

toolchain: $(TOOLSTAMP)

$(TOOLSTAMP):
	$(MAKE) config FLAVOUR=toolchain
	$(CMAKE) --build $(OBJ)toolchain --target unwind_static -- $(EXTRA)
	$(CMAKE) --build $(OBJ)toolchain --target cxxabi_static -- $(EXTRA)
	$(CMAKE) --build $(OBJ)toolchain --target cxx_static -- $(EXTRA)
	$(CMAKE) --build $(OBJ)toolchain --target cxx -- $(EXTRA)
	$(CMAKE) --build $(OBJ)toolchain --target clang -- $(EXTRA)
	mkdir -p $(CXX_STATIC)
	ln -sf $(CXX_LDIR)/libc++{,abi}.a $(CXX_STATIC)/
	touch $@

CURSES = libncursesw.a libncurses.a libcurses.a

${FLAVOURS:%=%-env}:
	$(MAKE) ${@:%-env=%} ${@:%-env=%}-llvm-utils
	env PATH=$(OBJ)toolchain/clang/bin:$(OBJ)${@:%-env=%}/llvm/bin:$(OBJ)${@:%-env=%}/tools:$$PATH \
		CXXFLAGS="$(CXXFLAGS_)" LDFLAGS="$(LDFLAGS_)" \
		DIVINE_BUILD_ENV="${@:%-env=%}" $$SHELL

env : ${DEFAULT_FLAVOUR}-env

show: # make show var=VAR
	@echo $($(var))

.PHONY: ${TARGETS} ${FLAVOURS} ${TARGETS:%=release-%} ${FLAVOURS:%=%-env}
.PHONY: toolchain validate dist env build config
.SILENT:
.NOTPARALLEL: # ignore -j

dist:
	darcs dist -d divine-$$(cat releng/version).$$(cat releng/patchlevel)$(VERSION_APPEND)

validate:
	$(MAKE) semidbg-divine
	$(MAKE) semidbg-test-divine
	$(OBJ)semidbg/divine/test-divine
	$(MAKE) semidbg-functional TAGS=min

${FLAVOURS:%=%-ext}:
	$(MAKE) ${@:%-ext=%} ${@:%-ext=%}-runner
	cd $(OBJ)${@:%-ext=%}/test && \
	   $(SETENV) SRCDIR=$(PWD) bash $(PWD)/test/lib/testsuite --testdir $(PWD)/test --only ext-

toolchain-install: toolchain
	$(CMAKE) --build $(OBJ)toolchain --target install -- $(EXTRA)

install: toolchain-install

prerequisites:
	sh ./releng/install-prereq.sh
