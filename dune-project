(lang dune 3.7)

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
  (dune-build-info
   (>= 3.7.0))
  (extlib
   (>= 1.7.9))
  (gen
   (>= 1.0))
  (linenoise
   (>= 1.4.0))
  (ocaml
   (>= 4.14))
  (sedlex
   (>= 2.5))
  (omd
   (>= 1.3.2))
  (uri
   (>= 4.2.0))
  (ocamlformat
   (and
    (= 0.25.1)
    :with-test))
  (yojson
   (>= 2.0.2))
  (ounit2
   (and
    (>= 2.2.6)
    :with-test))
  (bisect_ppx
   (and
    (>= 2.8.1)
    :with-test))
  (odoc
   (and
    (>= 2.2.0)
    :with-doc))))
