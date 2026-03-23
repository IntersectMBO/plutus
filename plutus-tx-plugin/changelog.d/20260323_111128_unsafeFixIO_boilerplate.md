### Changed

- The plugin now automatically sets the `Strict` extension and the GHC flags mentioned
  in https://plutus.cardano.intersectmbo.org/docs/using-plinth/extensions-flags-pragmas.
  The `Strict` extension can be turned off using plugin flag `no-strict`.
  Requires compiling with `plinthc` or `plc` instead of `compile`.
