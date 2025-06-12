# Compile a file to combinators, then tack it on to the C evaluator
# and compile the whole thing.
# Assume everything has been installed in $prefix.
# Depends on
#  $prefix/bin/mhseval
#  $prefix/lib/mhs/Tools/Compress.hs
#  $prefix/lib/mhs/Tools/Addcomb.hs
#  $prefix/lib/mhs/comb/mhs.comb
#  $prefix/lib/mhs/src/runtime/eval.c
#  $prefix/lib/mhs/lib/...
cc=gcc
here=`dirname $0`
prefix="${prefix:=.}"
prefixmhs="$prefix/lib/mhs"

compflags=""
output=""
while [ `expr "X$1" : "X-"` = "2" ]; do
    if [ `expr "$1" : "-o"` = "2" ]; then
        output="$1"
    else
        compflags="$compflags $1"
    fi
    shift
done
input="$1"
if [ -z "$input" ]; then
    echo "Usage: $0 [FLAGS] MODULE"
    exit 1
fi

lib="-i$prefixmhs/lib"

compile="$prefix/bin/mhseval +RTS -r$prefixmhs/comb/mhs.comb -RTS"
compress="$compile -r $lib -i$prefixmhs/Tools Compress"
addcomb="$compile -r $lib -i$prefixmhs/Tools Addcombs"

tmp=${TMPDIR:=/tmp}
tmpcomb=`mktemp $tmp/comb.XXXXXX`
tmpeval=`mktemp $tmp/eval.XXXXXX.c`

trap "rm -f $tmpcomb $tmpeval" EXIT

ex=""
$ex $compile $lib $compflags -o$tmpcomb "$input"
$ex cp $prefixmhs/src/runtime/eval.c $tmpeval
$ex $compress < $tmpcomb | $addcomb >> $tmpeval
$ex $cc -O3 $tmpeval $output
##$ex rm -f $tmpcomb $tmpeval
