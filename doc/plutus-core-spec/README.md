This directory contains a draft of a version of the Plutus Core specification
updated so that the language is parametric over a collection of built-in types
and functions.  It also updates the specification to reflect the fact that
built-in functions can now be partially applied.  ~Click
[here](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf)
to open a PDF of the most recent version of the specification in the main branch
of this repository.~  The link given in the previous sentence currently appears to be broken: would-be readers should build the PDF themselves.  On a Linux system, `make` in the main source directory should do this.

This version is currently restricted to untyped Plutus Core only. We will add a
specification of a typed version of Plutus Core at a later date.  For the time
being, please consult the [previous version](../plutus-core-spec-old) for
information about typed Plutus Core: this is somewhat outdated, but should give
the basic idea.
