#!/bin/bash

p=$PWD
for x in $(find . -type d -name "*-[0-9]")
do
    y=$(echo $x | sed 's|\(.\)$|0\1|')
    git mv $x $y
    cd $y
    for f in *[0-9].uplc*
    do
        g=$(echo $f | sed 's|\(.*\)\([0-9].uplc.*\)|\10\2|')
        git mv $f $g
    done
    cd $p
done
            

# Find all of the test directories with names like xyz-4
# Change into the directory
# Rename the ...-4.uplc... files to ...-04.uplc...
# Change up one directory
# Rename the directory to xyz-04

    

