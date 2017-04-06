# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind extlib ulex"

case "$OCAML_VERSION" in
4.00.1) ppa=avsm/ocaml40+opam12 ;;
4.01.0) ppa=avsm/ocaml41+opam12 ;;
4.02.1) ppa=avsm/ocaml42+opam12 ;;
*) echo Unknown $OCAML_VERSION; exit 1 ;;
esac

export OPAMYES=1
export OPAMVERBOSE=1
echo OCaml version
ocaml -version
echo OPAM versions
opam --version
opam --git-version

opam init
opam install ${OPAM_DEPENDS}
eval `opam config env`
make && ./TEST && (./TEST -- +htmltest) && (./TEST -- +sexp)
