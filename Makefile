DEBUG = true
#PROFILE = true
#WARN_PATTERN = true
#VERBOSE = 0
#BYTE = true
WARN_ERROR = true
PARALLEL = 4

EXT = $(if $(BYTE),byte,native)

OCAMLBUILD = ocamlbuild -r -use-ocamlfind \
	$(if $(PARALLEL),-j $(PARALLEL),) \
	$(if $(PROFILE),-tag profile,) \
	$(if $(DEBUG),-tag debug,) \
	$(if $(VERBOSE),-verbose $(VERBOSE),) \
	$(if $(WARN_PATTERN),-tag warn\(P\) -tag warn-error\(p\),)\
	$(if $(WARN_ERROR),-tag warn\(Azep-44-48-50-58\) -tag warn-error\(A-37-48-50-60\),)

.PHONY: all clean

all: bin/lex_dump bin/beluga bin/replay

bin/beluga: src/beluga/main.$(EXT)
	mkdir -p bin
	cp _build/$< $@

bin/lex_dump: src/beluga/lex_dump.$(EXT)
	mkdir -p bin
	cp _build/$< $@

bin/replay: src/beluga/replay.$(EXT)
	mkdir -p bin
	cp _build/$< $@

clean:
	$(OCAMLBUILD) -clean
	rm -rf bin

%:
	$(OCAMLBUILD) $@
