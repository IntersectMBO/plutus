
<a id='changelog-1.30.0.0'></a>
# 1.30.0.0 — 2024-06-17

## Removed

- Removed incorrect Ord and Eq instances from AssocMap and Data.AssocMap.

## Added

- Builtins corresponding to the logical operations from [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md).

- Builtin wrappers for operations from [this
  CIP](https://github.com/mlabs-haskell/CIPs/blob/koz/bitwise/CIP-XXXX/CIP-XXXX.md).

- Haskell `Eq` and `Ord` instances for `AssocMap` based on `Data.Map.Strict`.

## Changed

- References to CIP-0087 now correctly refer to CIP-121.

- Rename `replicateByteString` to `replicateByte`

<a id='changelog-1.29.0.0'></a>
# 1.29.0.0 — 2024-06-04

## Added

- Added `Data.AssocList.Map` module which provides a map implementation based on `Data`.

## Changed

- Split `PlutusTx.Builtins.Class` into `PlutusTx.Builtins.HasBuiltin` and `PlutusTx.Builtins.HasOpaque` in #5971:
+ Split 'FromBuiltin' into 'HasFromBuiltin' and 'HasFromOpaque'
+ Split 'ToBuiltin' into 'HasToBuiltin' and 'HasToOpaque'

- The PlutusTx `These` type had the Haskell implementations of `Show`, `Eq` and `Ord` instances instead of PlutusTx ones. This has been fixed.

<a id='changelog-1.28.0.0'></a>
# 1.28.0.0 — 2024-05-15

## Changed

- Renamed `PlutusTx.Builtins.matchList` to `matchList'`. The new `matchList` takes
  an argument of type `() -> r` for the `nil` case, ensuring that the nil case
  isn't evaluated if the list is non-empty.

<a id='changelog-1.26.0.0'></a>
# 1.26.0.0 — 2024-04-19

## Added

- CIP-0057 Blueprint generation is supported.

- An error code "PT20" for the `recip` function in the `PlutusTx.Ratio` module.

- `PlutusTx.List.indexBuiltinList`: index operator for builtin lists.

<a id='changelog-1.24.0.0'></a>
# 1.24.0.0 — 2024-03-26

## Added

- Documented functions which unsafely construct `PlutusTx.AssocMap.Map`s, or depend on the precondition that the input `Map`s do not contain duplicate entries.

## Changed

- Renamed `PlutusTx.AssocMap.Map.fromList` to `PlutusTx.AssocMap.Map.unsafeFromList`.
- Renamed `PlutusTx.AssocMap.Map.fromListSafe` to `PlutusTx.AssocMap.Map.safeFromList`.

<a id='changelog-1.22.0.0'></a>
# 1.22.0.0 — 2024-02-21

## Removed

- `PlutusTx.Ratio.reduce` removed in favor of `PlutusTx.Ratio.unsafeRatio` as it
was violating the "positive denominator" invariant.

## Added

- Builtins updated to include `ByteStringToInteger` and `IntegerToByteString`.

<a id='changelog-1.20.0.0'></a>
# 1.20.0.0 — 2024-01-15

## Added

- Entries in `PlutusTx.Builtins` for [CIP-0087
  primitives](https://github.com/mlabs-haskell/CIPs/blob/koz/to-from-bytestring/CIP-0087/CIP-0087.md)
- Entries in `PlutusTx.Builtins.Internal` for [CIP-0087
  primitives](https://github.com/mlabs-haskell/CIPs/blob/koz/to-from-bytestring/CIP-0087/CIP-0087.md)

## Fixed

- The `blake2b_224` function in the plutus-tx plugin was erroneously
  calling `blake2b_256` instead.  Now fixed.

<a id='changelog-1.19.0.0'></a>
# 1.19.0.0 — 2023-12-23

## Changed

- The group elements `bls12_381_G1_zero` and `bls12_381_G1_generator` have been replaced with bytestrings called `bls12_381_G1_compressed_zero` and `bls12_381_G1_compressed generator`, and similarly for `bls12_381_G2_zero` and `bls12_381_G2_generator`.  PlutusTx scripts should apply `bls12_381_G2_uncompress` or `bls12_381_G2_uncompress` to the compressed versions to recover the group elements.

- Improved the performance of `PlutusTx.AssocMap.insert` and `PlutusTx.AssocMap.unionWith`.

## Fixed

- The "safe" version of `fromData` was using an unsafe `head` function, so would
  crash on some malformed input instead of returning `Nothing`.

<a id='changelog-1.18.0.0'></a>
# 1.18.0.0 — 2023-12-06

## Added

- A more informative error message when the plugin encounters a literal range
- PlutusTx.enumFromThenTO for ranges like [1,5..101]

<a id='changelog-1.17.0.0'></a>
# 1.17.0.0 — 2023-11-22

## Changed

- Generated instances for `IsData` now have more efficient codegen, but
  require `ViewPatterns`.

<a id='changelog-1.13.0.0'></a>
# 1.13.0.0 — 2023-09-15

## Added

- `asData`, a TH function for creating datatype declarations
  that are backed by `Data`, which can be much faster in some
  circumstances.

- Generic instances for Rational and BuiltinData.

## Fixed

- Fixed a strictness issue in generated `IsData` instaces when using `-O0` in Plutus Tx.

<a id='changelog-1.12.0.0'></a>
# 1.12.0.0 — 2023-09-01

## Changed

- The `Strict` extension is now on by default in all of Plutus Tx.

<a id='changelog-1.10.0.0'></a>
# 1.10.0.0 — 2023-08-02

## Added

- Haskell function for `keccak_256` builtin
- Haskell function for `blake2b_224` builtin

<a id='changelog-1.8.0.0'></a>
# 1.8.0.0 — 2023-06-22

## Added

- New built-in types and functions for BLS12-381 operations.

<a id='changelog-1.7.0.0'></a>
# 1.7.0.0 — 2023-05-22

## Added

- GHC 9.6 support

## Changed

- Monomorphized functions in PlutusTx.Foldable that should short-circuit.
  This makes them short-circuit properly.

- `liftCode` and some other functions in `PlutusTx.Lift` now return PIR in addition to UPLC.

<a id='changelog-1.6.0.0'></a>
# 1.6.0.0 — 2023-05-04

## Changed

- Various `Lift` functions gained `Version` arguments, so that you can control the version of PLC used in the resulting program. This also affects how the PIR compiler will compile datatypes.

<a id='changelog-1.4.0.0'></a>
# 1.4.0.0 — 2023-03-23

## Added

- `unsafeApplyCode`, a variant of `applyCode` that throws if the language versions don't match.

## Changed

- `applyCode` now requires matching Plutus Core language versions.

<a id='changelog-1.3.0.0'></a>
# 1.3.0.0 — 2023-03-08

## Removed

- Removed Plutus Tx library functions with the `Haskell.Monad` constraint.
  Functions requiring `Functor` and `Applicative` are using `PlutusTx.Functor` and
  `PlutusTx.Applicative`, but those requiring `Monad` were using Haskell's `Monad`, which
  is inconsistent and confusing. We should either add a `PlutusTx.Monad` class, or switch
  to Haskell's `Functor` and `Applicative`. Some of these functions like `sequence_` and
  `mapM_` are also not useful, and one should prefer `sequenceA_` and `traverse_`, respectively.

## Changed

- Use `foldr` instead of `foldMap` in `PlutusTx.Foldable`
