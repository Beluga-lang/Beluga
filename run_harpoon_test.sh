#!/bin/bash

set -e

incomplete=0

function die() {
    echo $@ >&2
    exit 1
}

while (( $# )) ; do
    case "$1" in
        "--incomplete")
            incomplete=1
            ;;
        *)
            input_path="$1"
            break
            ;;
    esac
    shift
done

[ -z "${input_path}" ] && die "no input file specified"

sig=$(sed -n '1p' "${input_path}")
name=$(sed -n '2p' "${input_path}")
thm=$(sed -n '3p' "${input_path}")
order=$(sed -n '4p' "${input_path}")

shift

function the_rest() {
    if [ $incomplete -eq 0 ] ; then
        echo '/dev/null'
    else
        echo '-'
    fi
}

if test -n "$order" ; then
    rlwrap bin/harpoon --sig "${sig}" --name "${name}" --theorem "${thm}" --order "${order}" \
           --implicit \
           --test <(tail -n+5 "${input_path}") \
           $@
else
    rlwrap bin/harpoon --sig "${sig}" --name "${name}" --theorem "${thm}" \
           --implicit \
           --test <(tail -n+5 "${input_path}") \
           $@
fi
