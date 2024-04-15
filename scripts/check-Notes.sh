#!/usr/bin/env bash

# Run the `check-Notes.awk` script to make sure that Notes are properly
# formatted and cross-referenced.  See the awk file for a full description
# of the rules that are enforced.

# This script hould be run from the root of the Plutus repository.  It will
# return 1 if any problems are found and 0 otherwise.  To avoid quotation
# problems the Awk script is in its own file rather than being supplied as a
# command line argument to the `awk` command.

usage() {
    echo "usage: $0 [-l]"
    echo "Check the format of Notes in .hs files in the current directory and its"
    echo "subdirectories and report any problems, including invalid references."
    echo "   -l: include the file locations where undefined Notes are referenced."
}

for i in "$@"
do
    case $i in
       -l) # Print out locations as well as note titles.
          longOutput=1
          shift
          ;;
       *)
          usage
          exit 1
          ;;
    esac
done

files=$(find . -name "*.hs" | grep -v dist-newstyle)

if [ -z "$files" ]
then
    echo "Couldn't find any .hs files in $PWD"
    exit 1
fi


awk -f $(dirname $0)/check-Notes.awk -v longOutput="$longOutput" $files
