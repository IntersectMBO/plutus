These tests reproduce some of those in
[cardano-crypto-tests](https://github.com/IntersectMBO/cardano-base/tree/master/cardano-crypto-tests),
specifically the unit tests in [EllipticCurves.hs](https://github.com/IntersectMBO/cardano-base/blob/master/cardano-crypto-tests/src/Test/Crypto/EllipticCurve.hs).

The inputs to those tests (and hence these tests) were generated using the Rust
[bls12_381 library](https://docs.rs/bls12_381/latest/bls12_381/), so they
provide independent verification that the basic BLS12-381 functions (here
implemented using the [blst library](https://github.com/supranational/blst))
behave as expected.  Note that the test vectors provided in the [BLS12-381
specification](https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-bls-curves-for-the-128-bit-)
cannot be used because they are **incorrect**.

The other BLS12-381 conformance tests (in neighbouring directories of the
current one) test a wider range of properties, but their inputs were
chosen semi-randomly and their outputs were generated using the Plutus Core
implementations of the BLS12-381 built-in functions: thus they don't test
against some independent source of truth, although they do guard against changes
in the Plutus Core implementation and can be used to test other Plutus Core
evaluators for compatibilty with the standard one.  Also, there are
comprehensive property tests
[here](https://github.com/IntersectMBO/plutus/tree/master/plutus-core/untyped-plutus-core/test/Evaluation/Builtins)
which may be converted into conformance tests at some point in the future.
