find $1 -type f -name "*.bel" | while read bel; do
	TMP_FILE=`mktemp /tmp/config.XXXXXXXXXX`	
	sed -e 's/#infix/%infix/g' $bel > $TMP_FILE && mv $TMP_FILE $bel
	sed -e 's/#prefix/%prefix/g' $bel > $TMP_FILE && mv $TMP_FILE $bel
	sed -e 's/#opts/%opts/g' $bel > $TMP_FILE && mv $TMP_FILE $bel
	sed -e 's/#open/%open/g' $bel > $TMP_FILE && mv $TMP_FILE $bel
	sed -e 's/#assoc/%assoc/g' $bel > $TMP_FILE && mv $TMP_FILE $bel
	sed -e 's/%opts +strengthen;//g' $bel > $TMP_FILE && mv $TMP_FILE $bel
	sed -e 's/%opts -strengthen;/%nostrengthen/g' $bel > $TMP_FILE && mv $TMP_FILE $bel
done

