#!/bin/bash

p=$PWD
for x in $(find . -type d -name "*[a-z][0-9][0-9]")
do
    if [[ $x =~ Utf ]]; then continue; fi
    if [[ $x =~ crypto ]]; then continue; fi
    if [[ $x =~ nullList ]]; then continue; fi
    if [[ $x =~ chooseUnit ]]; then continue; fi
    y=$(echo $x | sed 's|\(..\)$|-\1|')
    git mv $x $y
    cd $y
    for f in *.uplc*
    do
        g=$(echo $f | sed 's|\(..*\)\([0-9][0-9].uplc.*\)|\1-\2|')
        git mv $f $g
    done
    cd $p
done
            

# Find all of the test directories with names like xyz-4
# Change into the directory
# Rename the ...-4.uplc... files to ...-04.uplc...
# Change up one directory
# Rename the directory to xyz-04

    

