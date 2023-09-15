### Changed

- Changed `PlutusLedgerApi.Common.ProtocolVersions.ProtocolVersion` to
  `PlutusLedgerApi.Common.ProtocolVersions.MajorProtocolVersion`. The ledger can only
  provide the major component of the protocol version (not the minor component), and
  Plutus should only care about the major component anyway.
