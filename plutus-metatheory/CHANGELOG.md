
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
