#!/bin/bash

set -u

sig=$(sed -n '1p' "$1")
name=$(sed -n '2p' "$1")
thm=$(sed -n '3p' "$1")
order=$(sed -n '4p' "$1")

path="$1"
shift

if test -n "$order" ; then
    tail -n+5 "${path}" |
        bin/harpoon --sig "${sig}" --name "${name}" --theorem "${thm}" --order "${order}" --implicit $@
else
    tail -n+5 "${path}" |
        bin/harpoon --sig "${sig}" --name "${name}" --theorem "${thm}" --implicit $@
fi
