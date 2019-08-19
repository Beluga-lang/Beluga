#!/usr/bin/env bash

set -eu

find "$1" -type f -name "*.bel" | while read -r bel; do
	TMP_FILE=$(mktemp /tmp/config.XXXXXXXXXX)
	sed -e 's/\[\s*\.\s*/[ |- /g' "${bel}" > "${TMP_FILE}" && mv "${TMP_FILE}" "${bel}"
	sed -e 's/\[\s*\([a-z]\)\s*\.\s*/[\1 |- /g' "${bel}" > "${TMP_FILE}" && mv "${TMP_FILE}" "${bel}"
	sed -e 's/\[\(\w*[,]\w*\)\.\s*/[\1 |- /g' "${bel}" > "${TMP_FILE}" && mv "${TMP_FILE}" "${bel}"
	sed -e 's/\[\(\(\s*\w*[,:(){}\&]\?'"'"'\?\s\?\(->\)\?\((\([\]\?\w*\s*[,:{}()&\]*'"'"'\?\(->\)\?\(\.\.\)\?\)*)\)*\)*[)}]\?\s*\)\.\([^.]\)/[\1 |- \8/g' "${bel}" > "${TMP_FILE}" && mv "${TMP_FILE}" "${bel}"
	sed -e 's/^\(\(\s*\w*[,:(){}\&]\?'"'"'\?\s\?\(->\)\?\((\([\]\?\w*\s*[,:{}()&\]*'"'"'\?\(->\)\?\(\.\.\)\?\)*)\)*\)*[)}]\?\s*\)\.\([^.].*\)\]/\1 |- \8]/g' "${bel}" > "${TMP_FILE}" && mv "${TMP_FILE}" "${bel}"
	sed -e 's/\(\\\w\+\s*\)|-/\1\./g' "${bel}" > "${TMP_FILE}" && mv "${TMP_FILE}" "${bel}"
done

