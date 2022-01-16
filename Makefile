.PHONY: all theories theories-32 install clean deepclean

all: theories


J?=4
BITSIZE?=opam

COQC=coqc
CLIGHTGEN?=clightgen

-include CONFIGURE

COQLIB=$(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')
COQLIBINSTALL=$(COQLIB)/user-contrib
ifeq ($(BITSIZE),64)
	COMPCERT_DIR=$(COQLIB)/user-contrib/compcert
	VST_DIR=$(COQLIB)/user-contrib/VST
	CERTIGRAPH_DIR=$(COQLIB)/user-contrib/CertiGraph
else ifeq ($(BITSIZE),32)
	CLIGHTGEN=$(COQLIB)/../../variants/compcert32/bin/clightgen
	COQLIBINSTALL=$(COQLIB)/../coq-variant/CertiGC32
	COMPCERT_DIR=$(COQLIB)/../coq-variant/compcert32/compcert
	VST_DIR=$(COQLIB)/../coq-variant/VST32/VST
	CERTIGRAPH_DIR=$(COQLIB)/../coq-variant/CertiGraph32/CertiGraph
endif

INSTALLDIR?=$(COQLIBINSTALL)/CertiGC

TARGET=x86_64-linux
ifeq ($(BITSIZE),32)
	TARGET=x86_32-linux
endif


theories/CertiGC/c/clightgen/x86_64-linux/gc.v: src/c/gc.c src/c/gc.h src/c/config.h src/c/mem.h
	mkdir -p `dirname $@`
	$(CLIGHTGEN) -Wall -Wno-unused-variable -Werror -normalize -o $@ src/c/gc.c

theories/CertiGC/c/clightgen/x86_32-linux/gc.v: src/c/gc.c src/c/gc.h src/c/config.h src/c/mem.h
	mkdir -p `dirname $@`
	$(CLIGHTGEN) -Wall -Wno-unused-variable -Werror -normalize -o $@ src/c/gc.c

_CoqProject: theories/CertiGC/c/clightgen/$(TARGET)/gc.v
	echo "# $(TARGET)"                                                          > $@
	@[ -z $(VST_DIR) ]          || echo "-Q $(VST_DIR) VST"                     >> $@
	@[ -z $(COMPCERT_DIR) ]     || echo "-Q $(COMPCERT_DIR) compcert"           >> $@
	@[ -z $(CERTIGRAPH_DIR) ]   || echo "-Q $(CERTIGRAPH_DIR) CertiGraph"       >> $@
	echo "-Q theories/CertiGC/model CertiGC.model"                              >> $@
	echo "-Q theories/CertiGC/c/ast CertiGC.c.ast"                              >> $@
	echo "-Q theories/CertiGC/c/clightgen/$(TARGET) CertiGC.c.clightgen"        >> $@
	echo "-Q theories/CertiGC/c/proof CertiGC.c.proof"                          >> $@
	echo "-Q theories/CertiGC/c/spec CertiGC.c.spec"                            >> $@
	find theories/CertiGC/model -name "*.v" | cut -d'/' -f1-                    >> $@
	find theories/CertiGC/c/ast -name "*.v" | cut -d'/' -f1-                    >> $@
	find theories/CertiGC/c/clightgen/$(TARGET) -name "*.v" | cut -d'/' -f1-    >> $@
	find theories/CertiGC/c/proof -name "*.v" | cut -d'/' -f1-                  >> $@
	find theories/CertiGC/c/spec -name "*.v" | cut -d'/' -f1-                   >> $@

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

clean:
	[ ! -f Makefile.coq ] || $(MAKE) -f Makefile.coq clean
	rm -f `find ./ -name "*Makefile.coq*"`
	rm -f `find ./ -name ".*.cache"`
	rm -f `find ./ -name "*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo*"`

deepclean: clean
	rm -f _CoqProject
