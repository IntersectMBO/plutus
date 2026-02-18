<!--
A new scriv changelog fragment.

Uncomment the section that is right (remove the HTML comment wrapper).
For top level release notes, leave all the headers commented out.
-->

<!--
### Removed

- A bullet item for the Removed category.

-->
<!--
### Added

- A bullet item for the Added category.

-->
### Changed

- String builtins (AppendString, EqualsString, EncodeUtf8, DecodeUtf8) now use
  byte-length costing for PV11+ (semvar D/E) via `TextCostingByteLength` newtype.
  Pre-PV11 behavior is unchanged. Cost model parameters re-benchmarked with
  corrected generators (removed stale text-1.x UTF-16 multiplier).

<!--
### Deprecated

- A bullet item for the Deprecated category.

-->
<!--
### Fixed

- A bullet item for the Fixed category.

-->

<!--
### Security

- A bullet item for the Security category.

-->
