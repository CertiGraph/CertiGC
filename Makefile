.PHONY: all theories theories-32 install clean deepclean

all: theories


J?=4
BITSIZE?=opam

COQC=coqc
CLIGHTGEN?=clightgen

-include CONFIGURE

COQLIB=$(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')
ifeq ($(BITSIZE),64)
	COMPCERT_DIR=$(COQLIB)/user-contrib/compcert
	VST_DIR=$(COQLIB)/user-contrib/VST
else ifeq ($(BITSIZE),32)
	COMPCERT_DIR=$(COQLIB)/../coq-variant/compcert32/compcert
	VST_DIR=$(COQLIB)/../coq-variant/VST32/VST
	CLIGHTGEN=$(COQLIB)/../../variants/compcert32/bin/clightgen
endif

TARGET=x86_64-linux
ifeq ($(BITSIZE),32)
	TARGET=x86_32-linux
endif


src/ast/x86_64-linux/gc.v: c/gc.c c/gc.h c/config.h c/mem.h
	$(CLIGHTGEN) -Wall -Wno-unused-variable -Werror -normalize c/gc.c -o src/ast/x86_64-linux/gc.v

src/ast/x86_32-linux/gc.v: c/gc.c c/gc.h c/config.h c/mem.h
	$(CLIGHTGEN) -Wall -Wno-unused-variable -Werror -normalize c/gc.c -o src/ast/x86_32-linux/gc.v

_CoqProject: src/ast/$(TARGET)/gc.v
	echo "-Q src/ast CertiGC.ast"                           		> $@
	echo "-Q src/ast/$(TARGET) CertiGC.ast.clightgen"    			>> $@
	echo "-Q src/model CertiGC.model"                       		>> $@
	echo "-Q src/proof CertiGC.proof"                       		>> $@
	echo "-Q src/spec CertiGC.spec"                         		>> $@
	@[ -z $(VST_DIR) ] 		|| echo "-Q $(VST_DIR) VST" 			>> $@
	@[ -z $(COMPCERT_DIR) ] || echo "-Q $(COMPCERT_DIR) compcert"	>> $@
	find ./ -name "*.v" | cut -d'/' -f2-                    		>> $@

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

theories: Makefile.coq
	$(MAKE) -f Makefile.coq -j$(J)

install:
	echo "TODO! ;0"

clean:
	[ ! -f Makefile.coq ] || $(MAKE) -f Makefile.coq clean
	rm -f `find ./ -name "*Makefile.coq*"`
	rm -f `find ./ -name ".*.cache"`
	rm -f `find ./ -name "*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo*"`

deepclean: clean
	rm -f _CoqProject