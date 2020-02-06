#!/usr/bin/env bash

set -euvx

eval "$(opam config env)"

./LINT
make
./TEST
./TEST -- +htmltest
