PROJECT=CertiGC


.PHONY: all theories install clean deepclean

all: theories


J?=4
BITSIZE?=opam
COQC?=coqc

-include CONFIGURE


COQLIB=$(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')
COQLIBINSTALL=$(COQLIB)/user-contrib

CLIGHTGEN64?=$(COQLIB)/../../bin/clightgen
CLIGHTGEN32?=$(COQLIB)/../../variants/compcert32/bin/clightgen

ifeq ($(BITSIZE),64)
	CERTIGRAPH_DIR=$(COQLIB)/user-contrib/CertiGraph
	VST_DIR=$(COQLIB)/user-contrib/VST
	COMPCERT_DIR=$(COQLIB)/user-contrib/compcert
else ifeq ($(BITSIZE),32)
	COQLIBINSTALL=$(COQLIB)/../coq-variant/$(PROJECT)-32
	CERTIGRAPH_DIR=$(COQLIB)/../coq-variant/CertiGraph32/CertiGraph
	VST_DIR=$(COQLIB)/../coq-variant/VST32/VST
	COMPCERT_DIR=$(COQLIB)/../coq-variant/compcert32/compcert
endif

INSTALLDIR?=$(COQLIBINSTALL)/$(PROJECT)

TARGET=x86_64-linux
ifeq ($(BITSIZE),32)
	TARGET=x86_32-linux
endif


theories/$(PROJECT)/c/clightgen/x86_64-linux/gc.v: src/c/gc.c src/c/gc.h src/c/config.h src/c/mem.h

theories/$(PROJECT)/c/clightgen/x86_32-linux/gc.v: src/c/gc.c src/c/gc.h src/c/config.h src/c/mem.h

theories/$(PROJECT)/c/clightgen/x86_64-linux/%.v:
	mkdir -p `dirname $@`
	$(CLIGHTGEN64) -Wall -Wno-unused-variable -Werror -normalize -o $@ $<

theories/$(PROJECT)/c/clightgen/x86_32-linux/%.v:
	mkdir -p `dirname $@`
	$(CLIGHTGEN32) -Wall -Wno-unused-variable -Werror -normalize -o $@ $<


_CoqProject: theories/$(PROJECT)/c/clightgen/$(TARGET)/gc.v
	echo "# $(TARGET)"                                                          > $@
	@[ -z $(VST_DIR) ]          || echo "-Q $(VST_DIR) VST"                     >> $@
	@[ -z $(COMPCERT_DIR) ]     || echo "-Q $(COMPCERT_DIR) compcert"           >> $@
	@[ -z $(CERTIGRAPH_DIR) ]   || echo "-Q $(CERTIGRAPH_DIR) CertiGraph"       >> $@
	echo "-Q theories/$(PROJECT)/model $(PROJECT).model"                        >> $@
	echo "-Q theories/$(PROJECT)/c/ast $(PROJECT).c.ast"                        >> $@
	echo "-Q theories/$(PROJECT)/c/clightgen/$(TARGET) $(PROJECT).c.clightgen"  >> $@
	echo "-Q theories/$(PROJECT)/c/proof $(PROJECT).c.proof"                    >> $@
	echo "-Q theories/$(PROJECT)/c/spec $(PROJECT).c.spec"                      >> $@
	find theories/$(PROJECT)/model -name "*.v" | cut -d'/' -f1-                 >> $@
	find theories/$(PROJECT)/c/ast -name "*.v" | cut -d'/' -f1-                 >> $@
	find theories/$(PROJECT)/c/clightgen/$(TARGET) -name "*.v" | cut -d'/' -f1- >> $@
	find theories/$(PROJECT)/c/proof -name "*.v" | cut -d'/' -f1-               >> $@
	find theories/$(PROJECT)/c/spec -name "*.v" | cut -d'/' -f1-                >> $@


Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

theories: Makefile.coq
	$(MAKE) -f Makefile.coq -j$(J)


C_SOURCES=$(shell find ./ -name "*.c" | cut -d'/' -f2-) $(shell find ./ -name "*.h" | cut -d'/' -f2-)
COQ_SOURCES=$(shell find ./ -name "*.v" | cut -d'/' -f2-)

INSTALL_SOURCES=$(C_SOURCES) $(COQ_SOURCES)
INSTALL_COMPILED=$(COQ_SOURCES:%.v=%.vo)

.PHONY: install
install:
	install -d "$(INSTALLDIR)"
	for d in $(sort $(dir $(INSTALL_SOURCES) $(INSTALL_COMPILED))); do install -d "$(INSTALLDIR)/$$d"; done
	for f in $(INSTALL_SOURCES) $(INSTALL_COMPILED); do install -m 0644 $$f "$(INSTALLDIR)/$$(dirname $$f)"; done


clightgen: \
	theories/$(PROJECT)/c/clightgen/x86_64-linux/gc.v \
	theories/$(PROJECT)/c/clightgen/x86_32-linux/gc.v


clean:
	[ ! -f Makefile.coq ] || $(MAKE) -f Makefile.coq clean
	rm -f `find ./ -name "*Makefile.coq*"`
	rm -f `find ./ -name ".*.cache"`
	rm -f `find ./ -name "*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo*"`

deepclean: clean
	rm -f _CoqProject
