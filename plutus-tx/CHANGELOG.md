# Revision history for `plutus-tx`

This format is based on [Keep A Changelog](https://keepachangelog.com/en/1.0.0).

## 0.2.0.0 -- 2021-12-13

### Added

* Specialized `abs` and `negate` for new `Rational` type, using much less
  on-chain space.

### Changed

* New implementation of `Rational`, which is more efficient on-chain.
* `abs`, `divMod` and `quotRem` now in `PlutusTx.Numeric`, as they're not
  specific to rational numbers.

### Removed

* `Ratio` data structure.
* `gcd` and `reduce` from `PlutusTx.Ratio`.
