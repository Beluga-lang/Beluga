DEBUG = true
#PROFILE = true
#WARN_PATTERN = true
#VERBOSE = 0
#BYTE = true
WARN_ERROR = true
PARALLEL = 4

# The binaries to build
# to add a new binary, which must correspond with an entry point file
# of the same name in src/beluga, simply list it here
BIN := beluga replay lex_dump lex_check

EXT = $(if $(BYTE),byte,native)

OCAMLBUILD = ocamlbuild -r -use-ocamlfind \
	$(if $(PARALLEL),-j $(PARALLEL),) \
	$(if $(PROFILE),-tag profile,) \
	$(if $(DEBUG),-tag debug,) \
	$(if $(VERBOSE),-verbose $(VERBOSE),) \
	$(if $(WARN_PATTERN),-tag warn\(P\) -tag warn-error\(p\),)\
	$(if $(WARN_ERROR),-tag warn\(Azep-44-48-50-58\) -tag warn-error\(A-37-48-50-60\),)

.PHONY: all clean $(BIN)

all: $(BIN)

$(BIN):
	mkdir -p bin
	$(OCAMLBUILD) src/beluga/$@.$(EXT)
	-rm bin/$@
	cp _build/src/beluga/$@.$(EXT) bin/$@

clean:
	$(OCAMLBUILD) -clean
	rm -rf bin
