.PHONY: all clean test all-test

all:
	dune build

test:
	dune exec ./TEST

all-test: test
	dune exec ./TEST -- +htmltest
	dune exec ./TEST -- +sexp

clean:
	dune clean
