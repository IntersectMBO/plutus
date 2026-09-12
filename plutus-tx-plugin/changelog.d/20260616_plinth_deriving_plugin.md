### Added

- The Plinth plugin now expands `deriving … via Plinth` clauses at parse time,
  generating `AsData` pattern synonyms, `Optics` prisms, and `Match` functions
  from data declarations. The pass is wired into `Plinth.Plugin`, so any module
  compiled with the Plinth plugin gets it automatically — no extra `-fplugin`.
  The implementation lives under `PlutusTx.Plugin.Deriving.*`, and the
  deriving-via sentinel type is `Plinth` (`PlutusTx.Plugin.Deriving.Via`).
