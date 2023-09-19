### Added

- Added a new data type `PlutusLedgerApi.Common.SerialisedScript.ScriptForEvaluation`,
  containing a serialised script and a deserialised script.

### Changed

- Renamed `PlutusLedgerApi.Common.SerialisedScript.ScriptForExecution` to
  `PlutusLedgerApi.Common.SerialisedScript.ScriptNamedDeBruijn`.
- Added a function `PlutusLedgerApi.Common.SerialisedScript.deserialiseScript`,
  which converts a `SerialisedScript` into a `ScriptForEvaluation`.
- Removed `PlutusLedgerApi.Common.SerialisedScript.fromSerialisedScript` and
  `PlutusLedgerApi.Common.SerialisedScript.assertScriptWellFormed`.
