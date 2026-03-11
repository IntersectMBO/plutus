### Added

- Source location tracking for the Agda certifier: the plugin now embeds
  `RealSrcSpan` information in `CompileContext` (`ccCurrentLoc`, `ccSourceLoc`)
  and passes it through to certificate generation via `ReaderT` instead of
  invasive function parameters.
- `--certify` plugin option to trigger Agda certificate generation for compiled
  Plutus scripts.
- `generateCertificate` top-level function that invokes the certifier with
  package name, module name, and source location metadata.

### Changed

- `compileExpr` no longer takes a `Maybe GHC.RealSrcSpan` parameter; source
  location now flows through `ccCurrentLoc` in `CompileContext` via
  `asks`/`local`.
- `compileMarkedExprs` simplified from a stateful `go lastLoc` loop to direct
  recursion.
- `stripAnchors` simplified to a single pattern match (no recursive `go` loop).
- Package name resolution uses `GHC.lookupUnit`, `GHC.thisPackageName`, and
  `stripVersionFromUnitId` as a fallback chain.

### Removed

- `findProjectRoot` — replaced by `System.Directory.makeAbsolute`.
