
<a id='changelog-1.68.1.0'></a>
# 1.68.1.0 — 2026-08-21

## Added

- Formalized `CInteger` and all of the `BuiltinInteger` functions which
depend on it.
- Removed the postulates for `divideInteger`, `modInteger`, `quotientInteger`
and `remainderInteger`, they are now implemented in the metatheory.
- Proved all the laws from the `QuotRemProperties` and `DivModProperties`
QuickCheck test suites as theorems in `Builtin.Integer.Properties`,
including the quotient-remainder round trips, sign and range laws, and the
additive/multiplicative homomorphism properties of `rem` and `mod`.
- Added `Maybe`-valued partial denotations of `quot`/`rem`/`div`/`mod` to
`Builtin.Integer.Base` (reused by `Builtin.CInteger`), exported them to
Haskell under stable names, and added the `test-integer-division` suite
property-testing the compiled Agda implementations against Haskell's
`quot`/`rem`/`div`/`mod`. The denotations are proved to agree with the total
operators on all non-zero divisors.

- Added casing on constants of builtin types (unit, bool, integer, list, pair)
  to the untyped CEK machine, mirroring the Haskell `CaseBuiltin DefaultUni`
  instance. The corresponding conformance tests now pass.

<a id='changelog-1.68.0.0'></a>
# 1.68.0.0 — 2026-08-18

## Fixed

- Fixed the Agda metatheory's `cekMachineCostFunction` calling `getCekConstCost` instead of `getCekConstrCost` for the `Constr` case, a copy-paste bug that would silently mis-cost `Constr`-containing terms once a cost-model update sets the two parameters apart.

- Fixed `chooseUnit`'s signature and typed CEK semantics having their arguments reversed (`forall a. a -> unit -> a` instead of the correct `forall a. unit -> a -> a`).
- Fixed `serialiseData` being an unbound postulate that crashed at runtime with "postulate evaluated" whenever actually called.

<a id='changelog-1.67.0.0'></a>
# 1.67.0.0 — 2026-08-06

## Added

- Postulated definitions for `Value` and its corresponding built-in functions

## Fixed

- Fixed a performance bug in the certifier regarding decidable equality.

<a id='changelog-1.65.0.0'></a>
# 1.65.0.0 — 2026-05-21

## Added

- The certifier now includes a README.md inside each generated Agda project, describing how to typecheck the certificate.

<a id='changelog-1.64.0.0'></a>
# 1.64.0.0 — 2026-05-11

## Changed

- `InvalidCertificate` error now includes the certifier report text for better
  diagnostics.
- Use `createDirectoryIfMissing` instead of `createDirectory` to avoid failures
  when certificate directories already exist.
- Removed noisy console output from `runCertifier` (result and path messages).

<a id='changelog-1.63.0.0'></a>
# 1.63.0.0 — 2026-05-01

## Removed

- Temporarily disabled the CSE certifier pass due to the discovery of bugs in the specification.

## Added

- Certifier for the case-reduce pass

- Certifier for the LetFloatOut pass

## Fixed

- Fixed the CSE translation relation in the certifier and re-enabled it.

<a id='changelog-1.62.0.0'></a>
# 1.62.0.0 — 2026-04-24

## Removed

- Temporarily disabled the CaseReduce certifier pass due to the discovery of bugs in the specification.

## Fixed

- The certifier reports now include the number of optimization sites for the force-case-delay pass as well.

<a id='changelog-1.61.0.0'></a>
# 1.61.0.0 — 2026-04-02

## Added

- Added a compiler certification pass for the force-case-delay optimization.

## Changed

- The certifier can now report execution budget before and after each pass.

<a id='changelog-1.60.0.0'></a>
# 1.60.0.0 — 2026-03-18

## Added

- Translation relation and decision procedure for the `ApplyToCase` pass.

<a id='changelog-1.50.0.0'></a>
# 1.50.0.0 — 2025-07-22

## Fixed

- Fixed broken unparsing of the list and pair Agda UPLC builtins in certificates.
