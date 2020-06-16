# Plutus Changelog

The format of this changelog is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## Unreleased

### Added

* Undo functionality in Marlowe Playground.
* Save/load to gist in Marlowe Playground.
* Playground usecases are multi-currency aware.
* Playground actions can be reordered with drag-and-drop.
* Tutorial and API documentation now hosted along with the Playgrounds, ensuring
  that they are in sync.
* Tutorial significantly updated and beautified.
* Plutus Tx support for "normal" function definitions, no need to use Template Haskell any more.
* The Plutus Tx Prelude is now a full Haskell Prelude replacement and should be used
  with `NoImplicitPrelude`.
* Typeclass support in Plutus Tx.
* More robust handling of newtypes in Plutus Tx. They should now incur no performance penalty.

### Changed

* 'Meadow' renamed to 'Marlowe Playground'
* Purescript version updated to 0.12.
* Significant and ongoing refactorings to ledger and wallet libraries to
  support integration into the Daedalus Smart Contract Backend.
* Validator scripts now return a `Bool` instead of indicating failure with `error`.
* Due to the removal of sized types, so the main integer type in Plutus Tx
  is now `Integer`, rather than `Int`.
* The Plutus Tx Prelude and the ledger and wallet libraries have been updated to use
  typeclasses and normal function definitions.

### Removed

* Removed sized types from Plutus Core.

### Fixed

* Scripts are now properly typechecked before being evaluated.
* Playground display of multi-currency values much improved.

## 2019-04-11

### Added

* [Gist integration](./changelog/Gist_integration.md).
* [Support for multiple traces](./changelog/Multiple_traces.md).
* [Multi-currency ledger](./changelog/Multi-currency_ledger.md).
* Tabbed layout.

### Changed

* [Validity range for transactions](./changelog/markdown/Validity_range_for_transactions.md).
* Improved blockchain graph.
* Improved vesting example.
* The order of arguments to the validator script has changed from `redeemerscript -> datascript -> PendingTx -> ()` to `datascript -> redeemerscript -> PendingTx -> ()`.

### Fixed

* Properly support cryptographic primitives in Plutus Core and Plutus Tx.
