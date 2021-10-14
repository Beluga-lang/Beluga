.PHONY: clean test all-test build doc

build:
	dune build

test: build
	dune runtest --force
	dune exec ./TEST

coverage:
	dune build --instrument-with bisect_ppx --force
	dune runtest --instrument-with bisect_ppx --force
	bisect-ppx-report html
	bisect-ppx-report summary

harpoon-test: build
	dune exec ./TEST -- --harpoon

all-test: test
	dune exec ./TEST -- +htmltest
	dune exec ./TEST -- +sexp

clean:
	dune clean

doc:
	make -C doc html
