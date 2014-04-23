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

clean:
	$(OCAMLBUILD) -clean

%:
	$(OCAMLBUILD) $@
