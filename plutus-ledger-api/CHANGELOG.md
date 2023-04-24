
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
