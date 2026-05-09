### Changed

- `InvalidCertificate` error now includes the certifier report text for better
  diagnostics.
- Use `createDirectoryIfMissing` instead of `createDirectory` to avoid failures
  when certificate directories already exist.
- Removed noisy console output from `runCertifier` (result and path messages).
