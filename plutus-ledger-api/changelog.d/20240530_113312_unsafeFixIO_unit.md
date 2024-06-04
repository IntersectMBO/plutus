### Changed

- `evaluateScriptRestricting` and `evaluateScriptCounting` now require Plutus V3
  scripts to return `BuiltinUnit`, otherwise the evaluation is considered to
  have failed, and a `InvalidReturnValue` error is thrown. There is no such
  requirement on Plutus V1 and V2 scripts.
