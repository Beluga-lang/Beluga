#!/usr/bin/env bash

set -euvx

eval "$(opam config env)"

opam install --deps-only .
