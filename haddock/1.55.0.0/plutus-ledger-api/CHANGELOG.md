
<a id='changelog-1.55.0.0'></a>
# 1.55.0.0 — 2025-11-11

## Added

- The two BLS12-381 multi-scalar multiplication functions
  `bls12_381_G1_multiScalarMul` and `bls12_381_G2_multiScalarMul` will become
  available on the chain at Protocol Version 11 once a protocol parameter update
  has taken place to add the relevant cost model parameters.

## Fixed

- Allows PlutusV3 scripts with the v1.0.0 Plutus Core language version.

<a id='changelog-1.54.0.0'></a>
# 1.54.0.0 — 2025-09-18

## Added

- Added the bls MSM built-in to plutus-core in #4255

<a id='changelog-1.51.0.0'></a>
# 1.51.0.0 — 2025-07-30

## Changed

- All built-in functions will be enabled in PlutusV1 and PlutusV2 in Protocol Version 11.
- Plutus Core version 1.1.0, and hence sums of products (the `case` and `constr` AST nodes), will be enabled in PlutusV1 and PlutusV2 in Protocol Version 11.

<a id='changelog-1.50.0.0'></a>
# 1.50.0.0 — 2025-07-22

## Added

- `PlutusLedgerApi.Envelope` module with two functions:
  - `compiledCodeEnvelope`: creates a JSON envelope for `CompiledCode` with a description.
  - `writeCodeEnvelope`: writes a JSON envelope for `CompiledCode` to a file.

<a id='changelog-1.46.0.0'></a>
# 1.46.0.0 — 2025-05-09

## Removed

- GHC 8.10 is no longer supported.  The supported GHC versions are 9.6 (primary), 9.8, and 9.10.

<a id='changelog-1.43.0.0'></a>
# 1.43.0.0 — 2025-03-20

## Added

- Added a Data-backed version of `MintValue` for Plutus V3.

## Changed

- The Data-backed V3 `ScriptContext` is updated to now use the Data-backed `MintValue`, similar to how the SOP `ScriptContext` uses the SOP `MintValue`.

<a id='changelog-1.42.0.0'></a>
# 1.42.0.0 — 2025-03-04

## Changed

-
- Remove un-needed dervied Typeable instances.

<a id='changelog-1.39.0.0'></a>
# 1.39.0.0 — 2024-12-20

## Added

- New data-backed versions of multiple modules in the ledger-api. These can be found in the `.../Data/` directories.

## Changed

- The `ScriptContext` types (`V1`, `V2` and `V3`) are now fully data-backed, meaning that all types contained in the data-backed version of the `ScriptContext` are also data-backed, except `Maybe` and `Bool`.
- In the case of the `V1` script context, in addition to `Maybe` and `Bool`, the pair type `(,)` is also kept as a SoP.

<a id='changelog-1.37.0.0'></a>
# 1.37.0.0 — 2024-11-25

## Added

- `PlutusLedgerApi.V1.withCurrencySymbol`

## Changed

- 'txInfoMint' function now returns 'MintValue' instead of 'Value' for minted values. This change
addresses problem described in the issue #5781.

- Changed data-backed version of the API to use `PlutusTx.Data.List`.

- Re-organize `PlutusLedgerApi.V1` exports: expose more bindings.

<a id='changelog-1.34.0.0'></a>
# 1.34.0.0 — 2024-09-09

## Added

- `HasBlueprintDefinition` and `HasSchemaDefinition` instances for data types.

<a id='changelog-1.33.0.0'></a>
# 1.33.0.0 — 2024-08-22

## Added

- A first version of a data-backed `ScriptContext`. The ledger API is similar to the regular `ScriptContext`; one should import the `Data` versions of modules instead to use this version. For example, `import PlutusLedgerApi.V2.Data.Contexts` instead of `import PlutusLedgerApi.V2.Contexts`, or `import PlutusLedgerApi.Data.V1` instead of `import PlutusLedgerApi.V1`.

- Guarded the draft 'modularExponentation' builtin behind a future protocol version.

- Builtin function `ripemd_160` implementing RIPEMD-160 hashing.

<a id='changelog-1.30.0.0'></a>
# 1.30.0.0 — 2024-06-17

## Added

- Added a new `Value` type backed by `Data`. This is currently experimental and not yet used in the ledger API.

- Exported the following from `PlutusLedgerApi.Common` in #6178:
  + `ExCPU (..)`
  + `ExMemory (..)`
  + `SatInt (unSatInt)`
  + `fromSatInt`
  + `toOpaque,
  + `fromOpaque`
  + `BuiltinData (..)`
  + `ToData (..)`
  + `FromData (..)`
  + `UnsafeFromData (..)`
  + `toData`
  + `fromData`
  + `unsafeFromData`
  + `dataToBuiltinData`
  + `builtinDataToData`

## Fixed

- Fixed the `Pretty` instance for `ScriptContext` to display the redemeer as well.

<a id='changelog-1.29.0.0'></a>
# 1.29.0.0 — 2024-06-04

## Added

- A new cost model for PlutusV3.

## Changed

- The `ScriptContext` type for Plutus V3 is modified to contain an optional datum for
  spending scripts, in the `scriptContextScriptInfo` field. The redeemer is now also
  part of `ScriptContext`. As a result, all Plutus V3 scripts, regardless of the purpose,
  take a single argument: `ScriptContext`.
- Datum is now optional for Plutus V3 spending scripts.

- We now have configurable cost models which allow different costs for different Plutus language versions and protocol versions.
- The `mkEvaluationContext` functions in `plutus-ledger-api` (which provide
  version-dependent on-chain configuration of the Plutus Core evaluator) now
  select appropriate cost models as well.

- `evaluateScriptRestricting` and `evaluateScriptCounting` now require Plutus V3
  scripts to return `BuiltinUnit`, otherwise the evaluation is considered to
  have failed, and a `InvalidReturnValue` error is thrown. There is no such
  requirement on Plutus V1 and V2 scripts.

<a id='changelog-1.27.0.0'></a>
# 1.27.0.0 — 2024-04-30

## Removed

- `Codec.CBOR.Extras` module is migrated from here to `plutus-core`.

## Changed

- `mkEvaluationContext` now takes `[Int64]` (instead of `[Integer]`).

`EvaluationContext` now contains:

- `PlutusLedgerLanguage` -- a ledger language
- `MajorProtocolVersion -> BuiltinSemanticsVariant DefaultFun` -- a function returning a semantics variant for every protocol version
- `[(BuiltinSemanticsVariant DefaultFun, DefaultMachineParameters)]` -- a cache of machine parameters for each semantics variant supported by the ledger language

Similarly, `mkDynEvaluationContext` now takes additional arguments:

- `PlutusLedgerLanguage` -- same as above
- `[BuiltinSemanticsVariant DefaultFun]` -- a list of semantics variants supported by the ledger language
- `MajorProtocolVersion -> BuiltinSemanticsVariant DefaultFun` -- same as above

All this allows us to improve the accuracy of costing in future protocol versions without introducing new ledger languages.

<a id='changelog-1.22.0.0'></a>
# 1.22.0.0 — 2024-02-21

## Added

- PlutusV3 cost model parameter names updated for `ByteStringToInteger` and `IntegerToByteString`.

- `PlutusLedgerApi.V1.Value.currencySymbolValueOf`, which calculates the total amount for
  the given `CurrencySymbol`.

## Changed

- Changed the `TxId`'s `BuiltingData` representation:
  removed a newtype constructor wrapping the underlying `BuiltinByteString`.

<a id='changelog-1.20.0.0'></a>
# 1.20.0.0 — 2024-01-15

## Changed

- More fields in the V3 script context use `Lovelace`

- Removed `GovernanceActionId` from the `Voting` script purpose. It is not needed because
  the script for a given voter will be run only once for all votes.

- Updated the `Certifying` and `Proposing` script purposes, whose arguments now consist of
  both an integer index and the actual argument (`TxCert` and `ProposalProcedure`).

- Updated the `NewCommittee` variant of `GovernanceAction` to `UpdateCommittee`.

<a id='changelog-1.19.0.0'></a>
# 1.19.0.0 — 2023-12-23

## Added

- Added functions for converting between `Lovelace` and `Value`: `lovelaceValue`
  and `lovelaceValueOf`.

- Added some helper functions for Plutus V3 ScriptContext.

## Changed

- Improved the efficiency of `PlutusLedgerApi.V1.Value.leq` and `PlutusLedgerApi.V1.Value.geq`.

- Use `Lovelace` instead of `Value` in `txInfoFee`, `txInfoCurrentTreasuryAmount`
  and `txInfoTreasuryDonation` for Plutus V3.

- Added constitution script hash to `ParameterChange` and `TreasuryWithdrawals`
  in the `ScriptContext` of Plutus V3.

<a id='changelog-1.18.0.0'></a>
# 1.18.0.0 — 2023-12-06

## Changed

- Added two constructors, `TxCertPoolRegister` and `TxCertPoolRetire`, to
  `PlutusLedgerApi.V3.Contexts.TxCert`.

<a id='changelog-1.17.0.0'></a>
# 1.17.0.0 — 2023-11-22

## Added

- Exposed `unSatInt` and `fromSatInt` from `plutus-ledger-api`. Added `NFData` and `NoThunks` for `CostModelApplyError`.

<a id='changelog-1.16.0.0'></a>
# 1.16.0.0 — 2023-11-10

## Changed

- Optimized equality checking of `Value`s in [#5593](https://github.com/IntersectMBO/plutus/pull/5593)

<a id='changelog-1.14.0.0'></a>
# 1.14.0.0 — 2023-09-28

## Added

- Added a new data type `PlutusLedgerApi.Common.SerialisedScript.ScriptForEvaluation`,
  containing a serialised script and a deserialised script.

## Changed

- Renamed `PlutusLedgerApi.Common.SerialisedScript.ScriptForExecution` to
  `PlutusLedgerApi.Common.SerialisedScript.ScriptNamedDeBruijn`.
- Added a function `PlutusLedgerApi.Common.SerialisedScript.deserialiseScript`,
  which converts a `SerialisedScript` into a `ScriptForEvaluation`.
- Removed `PlutusLedgerApi.Common.SerialisedScript.fromSerialisedScript` and
  `PlutusLedgerApi.Common.SerialisedScript.assertScriptWellFormed`.

- Changed `PlutusLedgerApi.Common.ProtocolVersions.ProtocolVersion` to
  `PlutusLedgerApi.Common.ProtocolVersions.MajorProtocolVersion`. The ledger can only
  provide the major component of the protocol version (not the minor component), and
  Plutus should only care about the major component anyway.

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
