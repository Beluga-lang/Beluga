#!/bin/bash

set -e

DEFAULT_LEXDUMP=0
if test -n "$LEXDUMP" ; then
    DEFAULT_LEXDUMP=1
    LEXDUMP="bin/lexdump"
fi

SYNOPSIS="Checks that the end of a file, as calculated by Beluga's \
lexer, coincides with the true end of the file, as calculated by the \
length of the file, in bytes.
If these counts do not match (for any of the specified files), this
script will exit with a nonzero status.\
Remark: the path to the lexdump program can be overridden by setting \
the environment variable \$LEXDUMP.
Currently, its value is: ${LEXDUMP}
This is $(test $DEFAULT_LEXDUMP -eq 0 && echo "not ") the default value."

USAGE="$(basename "$0") [--silent | --only-errors] FILES..."

usage () {
    echo "usage: $USAGE"
    echo "synopsis: $SYNOPSIS"
}

die () {
    if test -n "$@" ; then
        echo "$@" >&2
    fi
    exit 1
}

SILENT=0
ONLY_ERRORS=0

# use lex_dump to calculate where Beluga thinks the file ends.
beluga-eoi () {
    # The lex_dump output looks like:
    # EOI: 21-21
    bin/lex_dump "$1" | grep EOI | head -n 1 | cut -d " " -f2 | cut -d "-" -f1
}

true-eoi () {
    # wc output looks like:
    # 21 jake.bel
    wc -c "$1" | cut -d " " -f1
}

# Set to 1 when a failed file is detected.
FAILED=0

check-file () {
    local FILE="$1"
    local BELUGA_COUNT=$(beluga-eoi "$FILE")
    local TRUE_COUNT=$(true-eoi "$FILE")
    local EQ=$(test $BELUGA_COUNT -eq $TRUE_COUNT && echo "1" || echo "0")

    if [ $EQ -ne 1 ] ; then
        FAILED=1
    else
        # if the counts are in fact equal, but we're in errors-only
        # mode, then quit right away.
        if [ $ONLY_ERRORS -eq 1 ] ; then
            return 0
        fi
    fi

    if [ $SILENT -eq 1 ] ; then
        # return right away here if in silent mode, since the rest
        # of the function occupies itself with how to print the
        # result.
        return 0
    fi

    # If we make it here, it's because:
    # 1. we are not in silent mode; and
    # 2. we are in errors-only mode, but an error occurred; or
    # 3. we are not filtering the output at all

    echo -e "$FILE\t$BELUGA_COUNT\t$TRUE_COUNT"
}

CHECKING_FILES_NOW=0

checking-files-now () {
    if [ $CHECKING_FILES_NOW -eq 1 ] ; then
        usage
        die "Can't set $1 after starting to process files."
    fi
}

while (( $# )) ; do
    case "$1" in
        "--silent")
            checking-files-now "--silent"
            SILENT=1
            ;;
        "--only-errors")
            checking-files-now "--only-errors"
            ONLY_ERRORS=1
            ;;
        *)
            CHECKING_FILES_NOW=1
            check-file "$1"
            ;;
    esac
    shift
done

if [ $FAILED -eq 1 ] ; then
    exit 1
fi
