### Changed

- `compileUntyped` now encodes source locations in a structured null-separated
  format (matching `encodeSrcSpan` / `decodeSrcSpan`) instead of using
  `TH.pprint`, enabling the plugin to recover a `RealSrcSpan` from the
  type-level string.
