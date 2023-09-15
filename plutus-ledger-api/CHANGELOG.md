
<a id='changelog-1.13.0.0'></a>
# 1.13.0.0 — 2023-09-15

## Removed

- `evalCtxForTesting` in testlib: use instead `V*.mkEvaluationContext` with `V*.costModelParamsForTesting`

## Added

- Exported `ChangedParameters` in V3.

- costModelParamsForTesting for all plutus versions (PlutusV1,PlutusV2,PlutusV3)
- A `readParamName` method counterpart of the existing `showParamName`

## Changed

- `showParamName` method now operates on Text instead of previous String

## Fixed

- costModelParamsForTesting are now returned in the expected ledger order,
instead of alphabetical order

<a id='changelog-1.11.0.0'></a>
# 1.11.0.0 — 2023-08-24

## Added

- `ScriptContext` type for PlutusV3.

## Changed

- A CBOR script deserialization error now contains more descriptive (typed) errors,
  see `DeserialiseFailureInfo`.

- Updated `PlutusLedgerApi.V3.Contexts.ScriptContext`:
  - The `Proposing` `ScriptPurpose` now takes an `Integer` argument.
  - The `ParameterChange` `GovernanceAction` now takes a `ChangedParameters` argument.
  - `GovernanceActionId` is made optional in `GovernanceAction`.
  - `Anchor` is removed from `ScriptContext`.

<a id='changelog-1.10.0.0'></a>
# 1.10.0.0 — 2023-08-02

## Added

- cost model parameters for `keccak_256` builtin
- cost model parameters for `blake2b_224` builtin

<a id='changelog-1.8.0.0'></a>
# 1.8.0.0 — 2023-06-22

## Added

  - New entries for the BLS12-381 types and builtins

## Changed

  - The new built-in functions have been added to futurePV
    and the tests modified to deal with the additions.

<a id='changelog-1.7.0.0'></a>
# 1.7.0.0 — 2023-05-22

## Added

- GHC 9.6 support

<a id='changelog-1.6.0.0'></a>
# 1.6.0.0 — 2023-05-04

## Changed

- PlutusV3 is now allowed in protocol version 9.
- Plutus Core version 1.1.0 is now allwed in protocol version 9.

<a id='changelog-1.5.0.0'></a>
# 1.5.0.0 — 2023-04-16

## Changed

- `deserialiseUPLC` renamed to `uncheckedDeserialiseUPLC` since it doesn't do the checks for allowable builtins. This is dangerous in the ledger setting where this check is mandatory, so it needs a scarier name.

<a id='changelog-1.4.0.0'></a>
# 1.4.0.0 — 2023-03-23

## Added

- Support for multiple Plutus Core language versions.

## Changed

- The naming around "Plutus langauge versions" changed to talk about "Plutus ledger languages" following CIP-35.

<a id='changelog-1.3.0.0'></a>
# 1.3.0.0 — 2023-03-08

## Fixed

- Fixed numerous bugs in the behaviour of `Interval`s with open endpoints.

<a id='changelog-1.2.0.0'></a>
# 1.2.0.0 — 2023-02-24

## Added

- Exported `mkTermToEvaluate` from `PlutusLedgerApi/Common.hs`
