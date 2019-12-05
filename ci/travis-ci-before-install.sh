#!/usr/bin/env bash

set -euvx

echo "opam versions:" $(opam --version)$(opam --git-version)

opam init --bare

declare OCAML_FULL_VERSION=""
OCAML_FULL_VERSION=$(opam switch list-available "${OCAML_VERSION}" -s | grep 'ocaml-base-compiler' | sed 's/^[^.]*\.//g' | tail -n 1)

opam switch create "${OCAML_VERSION}" "${OCAML_FULL_VERSION}" ||
    opam switch set "${OCAML_VERSION}"
eval "$(opam config env)"

echo "OCaml version:" $(ocaml -version)
