all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject > Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
