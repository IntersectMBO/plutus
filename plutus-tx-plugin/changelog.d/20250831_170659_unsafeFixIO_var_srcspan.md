### Added

- During compilation, if a `Var` carries `SrcSpan`, the `SrcSpan` is added to the
  compilation trace. The effect can be seen both in the full compilation trace
  (via `dump-compilation-trace`), or in the error message when the compilation fails.
