### Removed

- Debugger executable is removed and integrated inside plutus executable.

### Added

- An experimental "plutus" tool that unifies `pir`, `plc`, `uplc`, and `debugger` executables into one.
- `Codec.CBOR.Extras` module is migrated here from `plutus-ledger-api.

### Fixed

- Restrict `eraseTerm`/`eraseProgram` to only work with `TPLC Name` input.
