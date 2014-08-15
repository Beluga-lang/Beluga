sed -i 's/#infix/%infix/g' $1
sed -i 's/#prefix/%prefix/g' $1
sed -i 's/#opts/%opts/g' $1
sed -i 's/#open/%open/g' $1
sed -i 's/#assoc/%assoc/g' $1
sed -i 's/%opts +strengthen;//g' $1
sed -i 's/%opts -strengthen;/%noStrengthen/g' $1
