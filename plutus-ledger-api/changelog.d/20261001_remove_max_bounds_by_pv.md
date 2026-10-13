### Changed

- The limits on constant type header size (32) and `constr` field count (1024)
  enforced when deserialising scripts now apply at every protocol version, rather
  than only from protocol version 11. It has been verified that no script ever
  submitted on-chain exceeds these limits, so this does not change the behaviour
  of any existing script.

### Removed

- `MaxBounds` and `maxBoundsByPV` from `PlutusLedgerApi.Common.Versions`,
  replaced by the constants `maxHeaderSize` and `maxConstrFields`.
