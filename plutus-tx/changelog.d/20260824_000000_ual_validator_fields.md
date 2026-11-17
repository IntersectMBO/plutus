### Added

- `PlutusTx.Blueprint.Validator.ValidatorBlueprint` gained three fields that are not part of
  CIP-57: `validatorId`, an optional identifier other documents can reference; `validatorArguments`,
  the ordered list of terms the compiled program is applied to, each an `AppliedArgument` pairing an
  `ArgumentEncoding` with a `Schema`; and `validatorBudget`, an optional `ExecutionBudget`. Each is
  omitted from the emitted JSON when absent or empty.
- `PlutusTx.Blueprint.Validator.mkValidatorBlueprint`, a `ValidatorBlueprint` with every optional
  field left out, to be refined with record-update syntax. Its `validatorRedeemer` is a bottom
  naming itself, since CIP-57 makes `redeemer` required and there is no honest default.

### Changed

- `MkValidatorBlueprint` gained three fields, so every record-construction site must either set them
  or switch to `mkValidatorBlueprint` with record-update syntax. The latter is recommended: further
  optional fields can then be added without breaking the call site.
- `ValidatorBlueprint`'s `validatorRedeemer` field is now lazy. Every other field in that module is
  strict, because the `plutus-tx` library is built with the `Strict` extension; the annotation is
  what lets `mkValidatorBlueprint` default the field to a bottom without the whole record being
  bottom.
- `PlutusTx.Blueprint.PlutusVersion.PlutusVersion` now derives `Lift`.
