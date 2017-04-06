# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind extlib ulex"

export OPAMYES=1
export OPAMVERBOSE=1
echo OCaml version
ocaml -version
echo OPAM versions
opam --version
opam --git-version

opam init
opam switch "$OCAML_VERSION"
opam install ${OPAM_DEPENDS}
eval `opam config env`
make && ./TEST && (./TEST -- +htmltest) && (./TEST -- +sexp)
