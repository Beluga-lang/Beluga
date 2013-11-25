INCLUDE_DIRS = src/core

CFLAGS = -I,src/core,-w,Aep-27-29-37,-warn-error,Ap-37

LFLAGS = -I,+camlp4,camlp4lib.cma

OCB = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(LFLAGS)

NLFLAGS = -I,+camlp4,camlp4lib.cmxa # ocamlfind cannot find the library for camlp4 so we provid it by hand
OCBN = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(NLFLAGS)

default: byte

native: beluga-native beli-native

byte: beluga-byte beli-byte

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

beli-native: corepack-native
	$(OCBN) src/beli/main.native

clean:
	ocamlbuild -clean
