#!/bin/sh

# ocamldoc generates the documentation HTML with the charset hardcoded
# to iso-8859-1.  Since we include UTF-8 characters in our comments,
# this makes them render improperly in the browser.  This fixes that.

ORIG=iso-8859-1
REPL=utf-8

grep -rl $ORIG $1 |
  while read fn
    do ( sed "s/$ORIG/$REPL/g;" $fn > $fn.xx
         mv $fn.xx $fn
       )
  done