#DEBUG = true
#PROFILE = true
#WARN_PATTERN = true
#VERBOSE = 0
#BYTE = true
PARALLEL = 4

OCAMLBUILD = ocamlbuild -use-ocamlfind \
	$(if $(PARALLEL),-j $(PARALLEL),) \
	$(if $(PROFILE),-tag profile,) \
	$(if $(DEBUG),-tag debug,) \
	$(if $(VERBOSE),-verbose $(VERBOSE),) \
	$(if $(WARN_PATTERN),-tag warn\(P\) -tag warn-error\(p\),)

.PHONY: all clean

all: all.otarget
	rm -f main.native
	mkdir -p bin
	ln -sf ../_build/src/beluga/main.native bin/beluga
	ln -sf ../_build/src/beli/main.native bin/beli

clean:
	$(OCAMLBUILD) -clean

%:
	$(OCAMLBUILD) $@
