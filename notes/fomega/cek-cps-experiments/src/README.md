This directory contains sources for various transformations of the CEK
machine. These are based on the earliest version in the repository
because it's the simplest and it should be easier to see any
performance differences due to the transformations.  I haven't
documented the source files carefully because they're just here for
the experiment.

`Make.hs` is a copy of
`plutus-core/src/Language/PlutusCore/Constant/Make.hs` with
the bounds check for sized integers updated to use bit operations
instead of computing 2^n arithmetically.  This was slowing things down
substantially and has now been fixed in the master branch, but hadn't
been fixed in the early version of the evaluator that we're basing things
on here.
