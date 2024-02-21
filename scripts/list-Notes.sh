#!/usr/bin/env bash

# Attempt to find Notes in Haskell source files and print out their titles,
# optionally accompanied by their locations.  You can restrict the output to
# those titles which only match a pattern supplied on the command line: eg
# `find-Notes.sh [bB]uilt`

usage() {
    echo "usage: $0 [-l] [target]"
    echo "Look for Notes in .hs files in the current directory and its"
    echo "subdirectories and print their titles."
    echo "   -l: include the file locations where the Notes are defined."
    echo "   target: an optional Awk pattern which Note titles must match."
}

for i in "$@"
do
    case $i in
       -l)
          longOutput=1
          shift
          ;;
       -*)
          usage
          exit 1
          ;;
       *)
          target="$i"
          shift
          ;;
    esac
done

files=$(find . -name "*.hs" | grep -v dist-newstyle)

if [ -z "$files" ]
then
    echo "Couldn't find any .hs files in $PWD"
    exit 1
fi

awk -f $(dirname $0)/list-Notes.awk -v longOutput="$longOutput" -v target="$target" $files | sort
