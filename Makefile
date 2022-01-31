.PHONY: clean test all-test build doc

build:
	dune build

test: build
	dune exec ./TEST

harpoon-test: build
	dune exec ./TEST -- --harpoon

all-test: test
	dune exec ./TEST -- +htmltest
	dune exec ./TEST -- +sexp

fmt:
	dune build @fmt --auto-promote

clean:
	dune clean

doc:
	make -C doc html
