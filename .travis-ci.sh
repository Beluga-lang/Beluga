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
opam switch "$OCAML_VERSION" || opam switch create "$OCAML_VERSION"
eval `opam config env`
opam install ${OPAM_DEPENDS}
make && ./TEST && (./TEST -- +htmltest) && (./TEST -- +sexp)
