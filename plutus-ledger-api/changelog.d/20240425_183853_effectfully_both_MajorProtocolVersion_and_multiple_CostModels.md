### Changed

`EvaluationContext` now contains:

- `PlutusLedgerLanguage` -- a ledger language
- `MajorProtocolVersion -> BuiltinSemanticsVariant DefaultFun` -- a function returning a semantics variant for every protocol version
- `[(BuiltinSemanticsVariant DefaultFun, DefaultMachineParameters)]` -- a cache of machine parameters for each semantics variant supported by the ledger language

Similarly, `mkDynEvaluationContext` now takes additional arguments:

- `PlutusLedgerLanguage` -- same as above
- `[BuiltinSemanticsVariant DefaultFun]` -- a list of semantics variants supported by the ledger language
- `MajorProtocolVersion -> BuiltinSemanticsVariant DefaultFun` -- same as above

All this allows us to improve the accuracy of costing in future protocol versions without introducing new ledger languages.
