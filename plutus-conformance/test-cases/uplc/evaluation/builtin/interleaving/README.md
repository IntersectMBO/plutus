The test cases here are all extracted from the tests in
`plutus-core/untyped-plutus-core/test/Evaluation/Golden.hs` and check that
interleaving of forces and normal arguments for builtin applications behaves
correctly.  Most of these are for `ifThenElse` (`ite`) because that has the most
complicated interleaving behaviour of our current builtins (it expects an
argument of the built-in `bool` type, then a `force`, then two term arguments).
