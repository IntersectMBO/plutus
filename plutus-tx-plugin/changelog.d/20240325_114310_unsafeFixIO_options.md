### Added

- Added two Plutus Tx compiler options, `preserve-logging` and `inline-constants`.
  Option `conservative-optimisation` implies (or negates) `relaxed-float-in`,
  `inline-constants` and `preserve-logging`, but previously only `relaxed-float-in` is
  a plugin option by itself.
