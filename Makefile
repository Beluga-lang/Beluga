
INCLUDE_DIRS = src/core

CFLAGS = -I,src/core

LFLAGS = -I,+camlp4,camlp4lib.cma

#OCB = ocamlbuild -classic-display -use-ocamlfind #-cflags $(CFLAGS)
OCB = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(LFLAGS)

#horrible, horrible, hack!
NLFLAGS = -I,+camlp4,camlp4lib.cmxa
OCBN = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(NLFLAGS)

default: corepack-native


corepack-byte:
	$(OCB) src/core/core.cmo # lib

beluga-byte: corepack-byte
	$(OCB) src/beluga/main.byte

beli-byte: corepack-byte
	$(OCB) src/beli/main.byte

####################
corepack-native:
	$(OCBN) src/core/core.cmx # lib

beluga-native: corepack-native
	$(OCBN) src/beluga/main.native

beli-native: corepack-native
	$(OCBN) src/beli/main.native

clean:
	ocamlbuild -clean
