# 0.5.0.0

=======
## Interface changes

 * Removed instances for machine-dependent ambiguous integer types `Int` and `Word`

## Added features

 * Support for `in_` on row values
 * Upsert support using `HasInsertOnConflict`
 * Fix build on Android and OpenBSD

## Bug fixes

 * Fix emitting and detection of `DECIMAL` and `DOUBLE PRECISION` types
 * Fix `bitLength`, `charLength_`, and `octectLength_` by emulating with `CAST` and `LENGTH`
 * Fix `runInsertReturningList` for when the database column order and beam column order disagree.

# 0.4.0.0

# 0.3.2.0

Add `Semigroup` instances to prepare for GHC 8.4 and Stackage nightly

# 0.3.1.0

Add `runBeamSqlite` and `runBeamSqliteDebug` functions

# 0.3.0.0

* Re-introduce backend parameter to `Database` class

# 0.2.0.0

First split of sqlite backend from main beam package
