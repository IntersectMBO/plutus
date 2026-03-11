### Added

- Source location tracking for the Agda certifier: the plugin now embeds
  `RealSrcSpan` information in `CompileContext` (`ccCurrentLoc`, `ccSourceLoc`)
  and passes it through to certificate generation via `ReaderT` instead of
  invasive function parameters.
- `certify` plugin option to trigger Agda certificate generation for compiled
  Plutus scripts.
- `generateCertificate` top-level function that invokes the certifier with
  package name, module name, and source location metadata.
