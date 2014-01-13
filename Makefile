INCLUDE_DIRS = src/core

CFLAGS = -I,src/core,-w,Aep-27-29-37,-warn-error,Ap-37-44

LFLAGS = -I,+camlp4,camlp4lib.cma

OCB = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(LFLAGS)

NLFLAGS = -I,+camlp4,camlp4lib.cmxa # ocamlfind cannot find the library for camlp4 so we provid it by hand
OCBN = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(NLFLAGS)

default: byte

native: bin-directory beluga-native beli-native

byte: bin-directory beluga-byte beli-byte

corepack-byte:
	$(OCB) src/core/core.cmo # lib

beluga-byte: corepack-byte
	$(OCB) src/beluga/main.byte
	mv main.byte bin/beluga

beli-byte: corepack-byte
	$(OCB) src/beli/main.byte
	mv main.byte bin/beli

corepack-native:
	$(OCBN) src/core/core.cmx # lib

beluga-native: corepack-native
	$(OCBN) src/beluga/main.native
	mv main.native bin/beluga

beli-native: corepack-native
	$(OCBN) src/beli/main.native
	mv main.native bin/beli

bin-directory:
	if ! [ -d bin ]; then mkdir bin; fi

clean:
	ocamlbuild -clean
	if [ -f bin/beli ]; then rm bin/beli; fi
	if [ -f bin/beluga ]; then rm bin/beluga; fi
	if [ -d bin ]; then rmdir bin; fi
