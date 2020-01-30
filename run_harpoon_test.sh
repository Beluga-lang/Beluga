#!/bin/bash

set -e

if [ $# -eq 0 ]; then
    echo "no input file specified" >&2
    exit 1
fi

declare -r input_path="$1"
shift

sig=$(sed -n '1p' "${input_path}")

exec ./bin/harpoon \
     --sig "${sig}" \
     --test "${input_path}" \
     --test-start 2 \
     $@
