.PHONY: build
build: # Build the public executables
	dune build @install

.PHONY: test
test: build # Build and run the OUnit2 test suite and the integration tests
	dune runtest --force
# TODO: dune exec ./TEST.sh

.PHONY: coverage
coverage: # Build and run the OUnit2 test suite and generate code coverage reports
	dune runtest --instrument-with bisect_ppx --force
	bisect-ppx-report html
	bisect-ppx-report summary

.PHONY: harpoon-test
harpoon-test: # Run only the Harpoon intergration tests
	./TEST.sh -- --harpoon

.PHONY: setup-development
setup-development: # Setup a development environment
	opam switch create --description="Beluga development switch" --locked --deps-only --with-test --with-doc --yes .

.PHONY: setup-install
setup-install: # Setup a user environment for installation
	opam switch create --description="Beluga installation switch" --locked --deps-only --yes .

.PHONY: install
install: # Build and install the public executables
	dune build @install && dune install

.PHONY: uninstall
uninstall: # Remove the built public executables
	dune uninstall

.PHONY: lock
lock: # Generate a lockfile for the dependencies in the opam repository
	opam lock --yes .

.PHONY: watch
watch: # Build default targets and trigger new builds on file system events
	dune build --watch

.PHONY: clean
clean: # Clean the files built by dune
	dune clean

.PHONY: fmt
fmt: # Format the codebase with ocamlformat
	dune build @fmt --auto-promote

.PHONY: doc
doc: clean # Generate the HTML documentations
	make -C doc html
	dune build @doc
