#!/bin/bash

set -e

incomplete=0

function die() {
    echo $@ >&2
    exit 1
}

input_path="$1"
shift
[ -z "${input_path}" ] && die "no input file specified"

sig=$(sed -n '1p' "${input_path}")

exec bin/harpoon \
     --sig "${sig}" \
     --implicit \
     --test "${input_path}" \
     --test-start 2 \
     $@
