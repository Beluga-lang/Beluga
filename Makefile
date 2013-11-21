
INCLUDE_DIRS = src/core

CFLAGS = -I,src/core

LFLAGS = -I,+camlp4,camlp4lib.cma

#OCB = ocamlbuild -classic-display -use-ocamlfind #-cflags $(CFLAGS)
OCB = ocamlbuild -Is $(INCLUDE_DIRS) -use-ocamlfind -cflags $(CFLAGS) -lflags $(LFLAGS)

default: beluga-byte


corepack-byte:
	$(OCB) src/core/core.cmo # lib

beluga-byte: corepack-byte
	$(OCB) src/beluga/main.byte

# BELUGA_DIRS = src/beluga
# BELI_DIRS = src/beli

# CFLAGS = -I,+extlib
# #CFLAGS =

# default: beluga-byte

# core-byte:
# 	ocamlbuild core.cmo

# core-native:
# 	ocamlbuild core.cmx

# beluga-native: #core-native
# 	ocamlbuild  -cflags $(CFLAGS) -Is $(BELUGA_DIRS) -use-ocamlfind main.native
# #	ocamlbuild  -Is $(BELUGA_DIRS) -use-ocamlfind -yaccflags --explain main.native

# beluga-byte: #core-byte
# 	ocamlbuild -cflags $(CFLAGS) -Is $(BELUGA_DIRS) -use-ocamlfind main.byte
# #	ocamlbuild $(OBFLAGS) -Is $(BELUGA_DIRS) -use-ocamlfind -yaccflags --explain main.byte

clean:
	ocamlbuild -clean
