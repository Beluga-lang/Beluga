(lang dune 3.6)

(name beluga)

(implicit_transitive_deps false)

(generate_opam_files true)

(license "GPL-3.0-only")

(authors
 "Brigitte Pientka"
 "Joshua Dunfield"
 "Andrew Cave"
 "Jacob Thomas Errington"
 "Junyoung Clare Jang"
 "Marc-Antoine Ouimet")

(maintainers "marc-antoine.ouimet@mail.mcgill.ca")

(homepage "http://complogic.cs.mcgill.ca/beluga/")

(source
 (github "Beluga-lang/Beluga"))

(package
 (name beluga)
 (synopsis
  "Implementation of contextual modal logic for reasoning with higher-order abstract syntax")
 (depends
  dune-build-info
  extlib
  gen
  linenoise
  (ocaml
   (>= 4.14))
  sedlex
  (yojson :with-test)
  (ounit2 :with-test)
  (bisect_ppx :with-test)))
