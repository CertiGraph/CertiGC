J?=4
CLIGHTGEN?=clightgen

.PHONY: all theories clean

all: theories

theories: Makefile.coq
	$(MAKE) -f Makefile.coq -j$(J)

# src/ast/x86_64-linux/gc.v: c/gc.c c/gc.h c/config.h c/mem.h
# 	$(CLIGHTGEN) -Wall -Wno-unused-variable -Werror -normalize c/gc.c -o src/gc.v

_CoqProject:
	echo "-Q src/ast CertiGC.ast"                           > _CoqProject
	echo "-Q src/ast/x86_64-linux CertiGC.ast.clightgen"    >> _CoqProject
	echo "-Q src/model CertiGC.model"                       >> _CoqProject
	echo "-Q src/proof CertiGC.proof"                       >> _CoqProject
	echo "-Q src/spec CertiGC.spec"                         >> _CoqProject
	find ./ -name "*.v" | cut -d'/' -f2-                    >> _CoqProject

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f `find ./ -name "*Makefile.coq*"`
	rm -f `find ./ -name "*.lia.cache"`
	rm -f `find ./ -name "*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo"`
	rm -f `find ./ -name "*.vok"`
	rm -f `find ./ -name "*.vos"`
