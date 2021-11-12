all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	+make -f Makefile.coq $@

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
aneris.opam: ;

.PHONY: all clean phony
