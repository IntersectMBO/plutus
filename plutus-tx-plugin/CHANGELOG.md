
<a id='changelog-1.41.1.0'></a>
# 1.41.1.0 — 2025-02-11

## Changed

- Changed the default value of compiler flag `PlutusTx.Plugin:preserve-logging` to true.

<a id='changelog-1.38.0.0'></a>
# 1.38.0.0 — 2024-12-09

## Removed

- `instance IsString TokenName` as it wasn't compilable by the plutus-tx-plugin anyway.
- `instance IsString CurrencySymbol` as it wasn't compilable by the plutus-tx-plugin anyway.

## Added

- `instance IsString BuiltinByteStringUtf8` allows using string literals to construct UTF8-encoded `BuiltinByteString` values.

- `instance IsString BuiltinByteStringHex` allows using string literals to construct Base16-encoded (aka HEX) `BuiltinByteString` values.

<a id='changelog-1.37.0.0'></a>
# 1.37.0.0 — 2024-11-25

## Changed

- `BuiltinByteString` literals changed to avoid UTF8 encoding and now can represent bytes in the range 0-255 directly, e.g. `"\x00\x01\x02" :: BuiltinByteString` or `stringToBuiltinByteString "\0\42\255"`.

<a id='changelog-1.34.0.0'></a>
# 1.34.0.0 — 2024-09-09

## Added

- A compiler flag `simplifier-evaluate-builtins` that controls whether to run the simplifier pass that evaluates fully saturated builtins at compile time.

<a id='changelog-1.33.0.0'></a>
# 1.33.0.0 — 2024-08-22

## Added

- Enabled the draft modularExponentation builtin.

<a id='changelog-1.27.0.0'></a>
# 1.27.0.0 — 2024-04-30


<a id='changelog-1.26.0.0'></a>
# 1.26.0.0 — 2024-04-19

## Added

- Added two Plutus Tx compiler options, `preserve-logging` and `inline-constants`.
  Option `conservative-optimisation` implies (or negates) `relaxed-float-in`,
  `inline-constants` and `preserve-logging`, but previously only `relaxed-float-in` is
  a plugin option by itself.

## Fixed

- Compiler flag `simplifier-remove-dead-bindings` does what it should now.

<a id='changelog-1.25.0.0'></a>
# 1.25.0.0 — 2024-04-03

## Changed

- (&&) and (||) now short-circuit regardless of the GHC optimisations.

<a id='changelog-1.22.0.0'></a>
# 1.22.0.0 — 2024-02-21

## Added

- Added `ByteStringToInteger` and `IntegerToByteString` builtins to the pluugin.

- added constant inlining to inlining optimisation passes

## Changed

- 'conservative-mode' now also turns off constant inlining

<a id='changelog-1.19.0.0'></a>
# 1.19.0.0 — 2023-12-23

- The group elements `bls12_381_G1_zero` and `bls12_381_G1_generator` have been replaced with bytestrings called `bls12_381_G1_compressed_zero` and `bls12_381_G1_compressed generator`, and similarly for `bls12_381_G2_zero` and `bls12_381_G2_generator`.  PlutusTx scripts should apply `bls12_381_G2_uncompress` or `bls12_381_G2_uncompress` to the compressed versions to recover the group elements.

<a id='changelog-1.18.0.0'></a>
# 1.18.0.0 — 2023-12-06

## Added

- A more informative error message when the plugin encounters a literal range.

## Changed

- Updated the Plutus Tx compiler to make the "Unsupported feature: Cannot case on a value on type"
  error happen less often (if not eliminating it entirely).

<a id='changelog-1.13.0.0'></a>
# 1.13.0.0 — 2023-09-15

## Added

- Better support for `RuntimeRep`-polymorphic code. In particular, this means we can
  now handle the code that GHC generates for pattern synonyms.

<a id='changelog-1.11.0.0'></a>
# 1.11.0.0 — 2023-08-24

## Added

- Add a new PlutusTx compiler option, `dump-compilation-trace`. It can be used to dump
  the full trace of compiling GHC `CoreExpr`s into PIR `Term`s for debugging.

## Fixed

- The plugin could generate exponentially large code from nested pattern matches with many default cases.
  This could happen when using pattern synonyms. This no longer happens.

<a id='changelog-1.8.0.0'></a>
# 1.8.0.0 — 2023-06-22

## Added

- New built-in types and functions for BLS12-381 operations.

<a id='changelog-1.7.0.0'></a>
# 1.7.0.0 — 2023-05-22

## Added

- GHC 9.6 support

<a id='changelog-1.6.0.0'></a>
# 1.6.0.0 — 2023-05-04

## Added

- `target-version` option that allows you to choose the target PLC version for the generated code.

<a id='changelog-1.3.0.0'></a>
# 1.3.0.0 — 2023-03-08

## Added

- `INLINE` pragmas from Haskell source are now propagated to Plutus IR, so they are guaranteed to be inlined.
