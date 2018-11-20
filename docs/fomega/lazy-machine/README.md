This directory contains a document describing the implementation of a lazy
abstract machine for Plutus Core and some benchmarking results for the lazy
machine and others.  To build the PDF, type `make`, or run 
`nix build -f default.nix docs.lazy-machine` from the root.

The `benchmarking` subdirectory contains scripts to run some timing benchmarks
and plot the results.  This will probably only work on Linux (or maybe OSX with
some extra work).  See `benchmarking/README.md` for more information
