
<a id='changelog-1.56.0.0'></a>
# 1.56.0.0 — 2025-11-27

## Removed

- PlutusTx.Ratio: half

## Added

- Enum Ratio instance that mimicks Haskell's instance

## Changed

- Renamed Ratio's fromGHC/toGHC to fromRatioHaskell/toRatioHaskell

- Made the (&&) and (||) operators short-circuit also in the Haskell side.
uplc code is unaffected and is already short-circuiting.

<a id='changelog-1.55.0.0'></a>
# 1.55.0.0 — 2025-11-11

## Changed

- Renamed 'Size' types functions to AstSize

<a id='changelog-1.54.0.0'></a>
# 1.54.0.0 — 2025-09-18

## Added

- Added the bls MSM built-in to plutus-core in #4255

<a id='changelog-1.53.0.0'></a>
# 1.53.0.0 — 2025-09-04

## Added

- Added Plinth builtin `caseInteger :: forall a. Integer -> [a] -> a`. Which will generate `Case` node that will case with the given integer as scrutinee and list as branches. This function expects it's second argument to be the Haskell list constructors. For example, `caseInteger 1 [1, 2, 3, 4]` will work, but `caseInteger 1 (id [1, 2, 3, 4])` won't work because the second argument is not a Haskell list constructor.

<a id='changelog-1.51.0.0'></a>
# 1.51.0.0 — 2025-07-30

## Changed

- Renamed `PlutusTx.Test.Util.compiledCodeToHask` to `PlutusTx.Test.Util.applyCodeN`
- Renamed `PlutusTx.Test.Util.compiledCodeToHaskUnsafe` to `PlutusTx.Test.Util.unsafeApplyCodeN`

<a id='changelog-1.50.0.0'></a>
# 1.50.0.0 — 2025-07-22

## Added

- Module 'PlutusTx.Test.Util.Compiled' of the 'plutus-tx-testlib' package got a new function 'countFlatBytes' that counts the size of a 'CompiledCode' in Flat bytes.

<a id='changelog-1.49.0.0'></a>
# 1.49.0.0 — 2025-07-08

## Added

- Module 'PlutusTx.Test.Util.Compiled' of the 'plutus-tx-testlib' package got a new function 'countFlatBytes' that counts the size of a 'CompiledCode' in Flat bytes.

<a id='changelog-1.47.0.0'></a>
# 1.47.0.0 — 2025-06-10

## Added

- `PlutusTx.Test.Run.Code` module was added to the `plutus-tx:testlib` package.
  This module provides a way to run compiled Plutus code in a test environment,
  allowing for easier testing and debugging of Plutus scripts. See more details in the User Guide.

- Added over 30 new functions to `PlutusTx.BuiltinList`

- Added new errors codes:
  - `PT23` -> `PlutusTx.BuiltinList.head: empty list`
  - `PT24` -> `PlutusTx.BuiltinList.tail: empty list`
  - `PT25` -> `PlutusTx.BuiltinList.last: empty list`

- Added TH help `PlutusTx.IsData.TH.makeIsDataAsList` which generates `ToData`, `FromData`, `UnsafeFromData` instances with internal representation being `Data.List` instead of `Data.Constr` for given product datatype(only having a single constructor).

- Added `PlutusTx.Test.Util.compiledCodeToHask` and `PlutusTx.Test.Util.compiledCodeToHaskUnsafe` for applying parameters to `CompiledCodeIn uni fun` tersely.

- Added `PlutusTx.Test.Golden.goldenCodeGen` for generating golden of the generated code from Template Haskell.

- Added `assertResult` for asserting given `CompiledCode Bool` evaluates `True`.

## Changed

- `BuiltinList` lookup is made cheaper by using the `DropList` builtin function.

<a id='changelog-1.46.0.0'></a>
# 1.46.0.0 — 2025-05-09

## Removed

- GHC 8.10 is no longer supported.  The supported GHC versions are 9.6 (primary), 9.8, and 9.10.

<a id='changelog-1.45.0.0'></a>
# 1.45.0.0 — 2025-04-15

## Added

- Module `PlutusTx.BuiltinList`, containing functions for operating on `BuiltinList`.

## Changed

- `PlutusTx.List.indexBuiltinList` is replaced by `PlutusTx.BuiltinList.!!`.

<a id='changelog-1.44.0.0'></a>
# 1.44.0.0 — 2025-04-03

## Removed

- Removed `Data.AssocMap.toDataList` because it suffers from the bug described in https://github.com/IntersectMBO/plutus/issues/6085.

## Added

- `PlutusTx.Data.List.destructList`, which takes a list along with a list of
  desired indices, and generates variables bound to the elements at those indices.

- `PlutusTx.Data.List.caseList` and `caseList'`, for matching on `List`s.

## Changed

- `PlutusTx.Lift.liftCode` and related functions now apply the default PIR and UPLC
  optimizations during code lifting. To disable these optimizations, use `liftCodeUnopt`
  and related functions.

- `PlutusTx.Prelude` no longer re-exports `PlutusTx.List`. There are now two separate
  list modules: `PlutusTx.List` and `PlutusTx.Data.List`. Pick the one that fits your
  use case and import it explicitly.

- `PlutusTx.Prelude` no longer re-exports `PlutusTx.Foldable` or `PlutusTx.Traversable`.
  These typeclasses are generally discouraged due to their performance overhead.
  For example, instead of using `PlutusTx.Foldable.foldMap`, consider rewriting
  your code using `PlutusTx.List.foldr`.

- `PlutusTx.Prelude` now re-exports `BuiltinBool`, `BuiltinList`, `BuiltinPair`,
  `ToData`, `FromData` and `UnsafeFromData`.

<a id='changelog-1.43.0.0'></a>
# 1.43.0.0 — 2025-03-20

## Added

- Added more standard library functions to `Data.List`.

- Added new conversion functions from Data-backed `Map` and Data-backed `List`.

- New `Data.AssocMap` library functions: `filter`, `mapWithKey`, `mapMaybe` and `mapMaybeWithKey`.

## Changed

- The conversion functions between `Data.AssocMap.Map` and different kinds of lists are now named according to which type of list they support.

- Slightly improved the performance of some of the existing `Data.AssocMap` functions.

<a id='changelog-1.42.0.0'></a>
# 1.42.0.0 — 2025-03-04

## Added

- `PlutusTx.Function.fix`, Plinth's equivalent of `Data.Function.fix`.

- Module `PlutusTx.Optimize.SpaceTime`, containing utilities for space-time tradeoff,
  such as recursion unrolling.

- Added `PlutusTx.Data.List.null`.

- Added `PlutusTx.Optimize.Inline.inline`. This works like `GHC.Magic.inline`, and can be used
  in the form of `inline f` or `inline (f args)`.

- Added more functions to PlutusTx.Data.List.

## Changed

-
- Remove un-needed dervied Typeable instances.

- Allow `PlutusTx.Optimize.Inline.inline` to inline local bindings.

- Removes the constructor id check from the code `AsData` generates for product types, resulting in better performance.

<a id='changelog-1.37.0.0'></a>
# 1.37.0.0 — 2024-11-25

## Added

- Added a data-backed list type in `PlutusTx.Data.List`.

<a id='changelog-1.36.0.0'></a>
# 1.36.0.0 — 2024-10-09

## Changed

- The type of `writeBits` built-in PlutusTx/Plinth function has been changed from

```
BuiltinByteString ->  [Integer] ->  [Bool] ->  BuiltinByteString
```

   to

```
BuiltinByteString ->  [Integer] ->  Bool ->  BuiltinByteString
```

   Instead of a list of boolean values to write to bit positions specified in the
   second argument it now takes a single boolean value which is used to update the
   bits at all of the given positions.  If it's necessary to set some bits and
   clear others then the function should be called twice, once with `True` as the
   third argument and once with `False`.

<a id='changelog-1.34.0.0'></a>
# 1.34.0.0 — 2024-09-09

## Changed

- CIP-57 (Blueprints) related changes:
  - `HasSchema` typeclass renamed to `HasBlueprintSchema`
  - `AsDefinitionId` typeclass renamed to `HasBlueprintDefinition`
  - `Unroll` type-family made into an associated type of `HasBlueprintSchema` in order to make it open for extension.
  - `HasBlueprintSchema` and `HasBlueprintDefinition` instances for data types.

<a id='changelog-1.33.0.0'></a>
# 1.33.0.0 — 2024-08-22

## Added

- Enabled the draft modularExponentation builtin.

- Builtin function `ripemd_160` implementing RIPEMD-160 hashing.

<a id='changelog-1.32.0.0'></a>
# 1.32.0.0 — 2024-08-06

## Changed

- In #6347 made `[] :: [Integer]`, `[] :: [Bool]`, `[] :: [Data]`, and `[(Data, Data)]` compile directly to the respective empty list via the `MkNil` type class without usage of built-in functions or `defineBuiltinTerm`.

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
