
<a id='changelog-1.11.0.0'></a>
# 1.11.0.0 — 2023-08-24

## Added

- Optimization pass to strictify bindings

<a id='changelog-1.10.0.0'></a>
# 1.10.0.0 — 2023-08-02

## Added

- `keccak_256` builtin
- `blake2b_224` builtin

## Changed

- Separated the single `Includes` constraint into two constraints, `HasTypeLevel` and `HasTermLevel` (which together form `HasTypeAndTermLevel`) in #5434.

<a id='changelog-1.9.0.0'></a>
# 1.9.0.0 — 2023-07-21

## Changed

- Flat serialization&deserialization of DeBruijn indices go directly via Word64,
instead of the previous indirection via Natural.

## Fixed

- The `FakeNamedDeBruijn`'s `encode`&`size` methods  are fixed to roundtrip its flat format

<a id='changelog-1.8.0.0'></a>
# 1.8.0.0 — 2023-06-22

## Added

- Three new types for BLS12-381 objects (see CIP-0381).
- Seventeen new built-in functions for BLS12-381 operations (see CIP-0381).
- Costing benchmarks for the BLS12-381 builtins.
- R code to infer cost models for the BLS12-381 builtins.
- Property tests for the BLS12-381 builtins.
- Code for Haskell bindings to the`blst` library has been added in `cbits` and
  `plutus-core/src/Crypto/External/`.  These have been copied from PR #266
  in `cardano-base` and will be removed when that is merged.

- A special case of case-of-case optimization for UPLC, where the inner case is
  an `ifThenElse` application.

- Added `PlutusCore.MkPlc.mkIterAppNoAnn`, `PlutusCore.MkPlc.mkIterInstNoAnn` and
  `PlutusCore.MkPlc.mkIterTyAppNoAnn`.

- Callsite inlining for UPLC.

- An `apply-to-data` command was added to the `plc` and `uplc` executables which
  allows a script to be applied to a list of flat-encoded data objects (the
  existing `apply` command requires all inputs to be programs).

- Added `commuteFnWithConst` to the PIR simplifier pass.

## Changed

- The PLC, UPLC, and PIR parsers accept names quoted in backticks. Quoted names may have symbolic characters.

- Costing functions for the BLS12-381 builtins were added to `builtinCostModel.json`.
- Costing benchmark results for the BLS12-381 builtins were added to `benching.csv`.
- Some of the R code in `models.R` was improved.
- The files in `plutus-core/src/crypto` were reorganised to put code relating to
  different sets of crypto functions into separate files.

- Improved the inlining of fully saturated functions such that it measures the size
  differences more accurately, and also performs beta reduction after inlining.

- Changed `PlutusCore.MkPlc.mkIterApp`, `PlutusCore.MkPlc.mkIterInst` and
  `PlutusCore.MkPlc.mkIterTyApp` to require an annotation to be provided
  for each argument.

- Updated the parser and the pretty-printers to the new syntax of `Data` in [#5391](https://github.com/input-output-hk/plutus/pull/5391) according to [this](https://github.com/input-output-hk/plutus/issues/4751#issuecomment-1538377273), for example:

```
Constr 1
  [ Map [(B #616263646566, Constr 2 [B #, I 0])]
  , List
      [ List
          [ List [List [I 123456]]
          , B #666666666666666666666666666666666666666666666666666666666666666666666666666666666666 ] ]
  , I 42 ]
```

## Fixed

- The plc and uplc commands were failing to account for the new Constr and Case
  constructors for sums of products.

- Fixed `PlutusIR.Purity.firstEffectfulTerm` and `UntypedPlutusCore.Transform.Inline.firstEffectfulTerm`,
  which were sometimes too conservative and sometimes incorrect.

<a id='changelog-1.7.0.0'></a>
# 1.7.0.0 — 2023-05-22

## Added

- Float Delay optimization for UPLC.

- GHC 9.6 support

## Changed

- Improved "readable" pretty-printing functions by making them insert line breaks properly
- Simplified using "readable" pretty-printing by introducing the `PlutusCore.Pretty.Readable.AsReadable` wrapper

## Fixed

- The PIR executable now actually checks uniqueness when reading a program.

- `applyProgram` and `applyCode` now return `Either` instead of `Maybe` for better error messages.

<a id='changelog-1.6.0.0'></a>
# 1.6.0.0 — 2023-05-04

## Added

- Case-of-known-constructor for Plutus IR.

- The Plutus IR compiler can now compile datatypes using SOPs.

- Generic builtin evaluation pass for PIR (subsumes constant-folding).

## Changed

- Various `intercept` and `slope` constants are now wrapped in `Intercept` and `Slope` `newtype`s

## Fixed

- The inliner now rename before call site inlining to ensure global uniqueness.

<a id='changelog-1.5.0.0'></a>
# 1.5.0.0 — 2023-04-16

## Removed

- `Flat` instances for UPLC terms and programs. These were potentially unsafe as they don't perform the builtin checks that are required on chain, so it is important not to use them by accident.

## Added

- `optimise` options for the `pir`, `plc`, and `uplc` commands.
- A `compile` option for the `pir` command which allows a PIR file to be
  compiled to PLC or UPLC.
- Functions for mapping over names and typenames in the PLC AST.

- Inlining of fully applied functions in the PIR inliner. This only affects non-recursive bindings.

- Plutus Core 1.1.0 now supports sums-of-products via the new `constr` and `case` terms. See CIP-85 for details.

- `UnrestrictedProgram` newtype that performs unchecked serialization/deserialization of programs for when that's appropriate.

- Tests for Steppable CEK against original CEK

## Changed

- Some of the `pir` commands have been extended to allow both `flat` and textual
  input.

- Made costing lazier to speed things up and increase expressiveness. #5239

## Fixed

- Fixed the `safeEncodeBits` assertion to also guard against 1 unsafe case. Does not affect current encoding/decoding.

<a id='changelog-1.4.0.0'></a>
# 1.4.0.0 — 2023-03-23

## Added

- New Plutus Core language version 1.1
- PIR programs now have a version, which corresponds to the underlying Plutus Core language version.

## Changed

- `defaultVersion` renamed to `latestVersion`
- `applyProgram` now merges annotations and requires matching program versions

- Use a primitive array for the step counter; removed the word-array package.

<a id='changelog-1.3.0.0'></a>
# 1.3.0.0 — 2023-03-08

## Added

- The debugger TUI updates live the currently spent CPU&MEM resources of the debugged program.
- The debugger TUI accepts a `--budget` to limit the CPU&MEM resources of the debugged program.

## Changed

- The PIR readable prettyprinter was improved in a number of minor ways.

<a id='changelog-1.2.0.0'></a>
# 1.2.0.0 — 2023-02-24

## Added

- Added `NoThunks` instance for `Data`.

- A float-in compilation pass, capable of floating term bindings inwards in PIR. See Note [Float-in] for more details.

- Tests targeting testing of (1) unconditional inlining of functions (2) call site inlining of fully applied functions (for the upcoming implementation).

- The debugger can now highlight (beside the UPLC expression), the original PlutusTX expression
  currently being evaluated.

- The debugger driver will now capture any error during the stepping of a PLC program and
  display it inside the debugging clients (tui,cli,etc).

- function to track the type and term lambda abstraction order of a term in the PIR inliner.

## Changed

- PIR, TPLC and UPLC parsers now attach `PlutusCore.Annotation.SrcSpan` instead of
  `Text.Megaparsec.Pos.SourcePos` to the parsed programs and terms.

- The float-in pass can now float non-recursive type and datatype bindings.

- The float-in pass now floats bindings inwards more aggressively.
  See Note [Float-in] #5.

- Plutus IR was moved to a public sub-library of `plutus-core`.

- `Version` no longer has an annotation, as this was entirely unused.

- Made `geq` faster in certain cases, -1% of total validation time. [#5061](https://github.com/input-output-hk/plutus/pull/5061)

- Made the Haskell-Tx file input to the debugger optional.

## Fixed

- The `goldenPIR` function now uses the correct function to print parse errors, so they are now printed in a human-readable way.

- PIR, PLC and UPLC term parsers can now parse comments.
