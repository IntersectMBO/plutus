### Removed

- `unsafeRunCekNoEmit` and all `unsafeEvaluate*` functions in #6043. To replace e.g. `unsafeEvaluateCek` you can use `evaluateCek` in combination with `unsafeToEvaluationResult`.

### Changed

- Renamed `unsafeExtractEvaluationResult` to `unsafeToEvaluationResult`.
