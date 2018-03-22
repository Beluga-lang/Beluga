#!/bin/bash

make bin/lex_dump
find examples -type f -name '*.bel' | xargs ./lex_check.sh --only-errors
