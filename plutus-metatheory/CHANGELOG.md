
<a id='changelog-1.65.0.0'></a>
# 1.65.0.0 — 2026-05-21

## Added

- The certifier now includes a README.md inside each generated Agda project, describing how to typecheck the certificate.

<a id='changelog-1.64.0.0'></a>
# 1.64.0.0 — 2026-05-11

## Changed

- `InvalidCertificate` error now includes the certifier report text for better
  diagnostics.
- Use `createDirectoryIfMissing` instead of `createDirectory` to avoid failures
  when certificate directories already exist.
- Removed noisy console output from `runCertifier` (result and path messages).

<a id='changelog-1.63.0.0'></a>
# 1.63.0.0 — 2026-05-01

## Removed

- Temporarily disabled the CSE certifier pass due to the discovery of bugs in the specification.

## Added

- Certifier for the case-reduce pass

- Certifier for the LetFloatOut pass

## Fixed

- Fixed the CSE translation relation in the certifier and re-enabled it.

<a id='changelog-1.62.0.0'></a>
# 1.62.0.0 — 2026-04-24

## Removed

- Temporarily disabled the CaseReduce certifier pass due to the discovery of bugs in the specification.

## Fixed

- The certifier reports now include the number of optimization sites for the force-case-delay pass as well.

<a id='changelog-1.61.0.0'></a>
# 1.61.0.0 — 2026-04-02

## Added

- Added a compiler certification pass for the force-case-delay optimization.

## Changed

- The certifier can now report execution budget before and after each pass.

<a id='changelog-1.60.0.0'></a>
# 1.60.0.0 — 2026-03-18

## Added

- Translation relation and decision procedure for the `ApplyToCase` pass.

<a id='changelog-1.50.0.0'></a>
# 1.50.0.0 — 2025-07-22

## Fixed

- Fixed broken unparsing of the list and pair Agda UPLC builtins in certificates.
