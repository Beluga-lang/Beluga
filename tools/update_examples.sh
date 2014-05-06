#!/bin/sh
#This script changes "." to "|-"
#Run the script against the directories containing the .bel files you'd like to update
find $1 -type f -name "*.bel" | while read bel; do
	sed -i 's/\[\s*\.\s*/[ |- /g' $bel
	sed -i 's/\[\s*\([a-z]\)\s*\.\s*/[\1 |- /g' $bel
	sed -i 's/\[\(\w*[,]\w*\)\.\s*/[\1 |- /g' $bel
	sed -i 's/\[\(\(\s*\w*[,:(){}\&]\?'"'"'\?\s\?\(->\)\?\((\([\]\?\w*\s*[,:{}()&\]*'"'"'\?\(->\)\?\(\.\.\)\?\)*)\)*\)*[)}]\?\s*\)\.\([^.]\)/[\1 |- \8/g' $bel
	sed -i 's/^\(\(\s*\w*[,:(){}\&]\?'"'"'\?\s\?\(->\)\?\((\([\]\?\w*\s*[,:{}()&\]*'"'"'\?\(->\)\?\(\.\.\)\?\)*)\)*\)*[)}]\?\s*\)\.\([^.].*\)\]/\1 |- \8]/g' $bel
	sed -i 's/\(\\\w\+\s*\)|-/\1\./g' $bel


done

