
<a id='changelog-1.2.0.0'></a>
# 1.2.0.0 — 2023-02-16

## Added

- Added `NoThunks` instance for `Data`.

- A float-in compilation pass, capable of floating term bindings inwards in PIR. See Note [Float-in] for more details.

- The debugger can now highlight (beside the UPLC expression), the original PlutusTX expression
  currently being evaluated.

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
