# `generate-agda-conformance`

This tool turns the UPLC evaluation conformance test cases in
`plutus-conformance/test-cases/uplc/evaluation` into Agda unit tests under
`plutus-metatheory/src/Conformance/`. For each test case it generates a proof
that the Agda CEK machine gives the expected result. Agda checks those proofs
when it type-checks the module, so a test "runs" when you type-check
`Conformance.lagda.md`. The implementation is described in the header of
[`Main.hs`](Main.hs) and in `Conformance.Eval` in the metatheory.

Regenerate the tests from the nix shell with

    generate-agda-conformance

or, without nix, from the repository root with

    cabal run plutus-conformance:generate-agda-conformance

A pre-push hook regenerates them when the test cases, this tool, or
`plutus-metatheory/src/{Conformance,FFI}` change.

## Why this exists: compile-time vs runtime Agda

There are two ways to run the Agda semantics against the same conformance test
cases, and they test different things:

- **`agda-conformance`** (`plutus-conformance/agda/Spec.hs`) runs the Agda
  evaluator **at runtime**. The metatheory is compiled to Haskell with MAlonzo,
  and the Haskell test harness parses each program, converts it into the
  MAlonzo representation, runs the compiled CEK machine, converts the result
  back, and compares it with the expected output. Budgets are checked too.
- **The generated `Conformance.*` modules** run the Agda evaluator **at
  type-checking time**. Each test is stated as
  `evalRaw test-x ≡ expected-x` and proved by `refl`, so Agda's normaliser has
  to evaluate the program using the Agda *definitions* of the CEK machine and
  of the builtins. Nothing is compiled and no Haskell code runs.

### What is tested

A `refl` test checks that, for a closed program `t` with expected result `r`
(`success v` or `failure`):

- `t` and `v` are well-formed Agda terms of type `Untyped`. The Haskell parser
  reads the `.uplc` files and the FFI unparser (`FFI.AgdaUnparse`) prints them
  as Agda source.
- scope-checking `t`, running `Untyped.CEK.stepper` on it with the same step
  budget (`maxsteps`) as the compiled evaluator, and discharging the final
  value gives exactly `r`, compared syntactically on de Bruijn terms.

It does **not** test costing (there is no budget check), the MAlonzo
compilation, the `COMPILE` pragmas, or the Haskell↔Agda term conversion used
at runtime.

### Pending and skipped tests

Some cases cannot be proved by `refl`. The generator classifies them using
the tables at the top of `Main.hs`:

- **Pending**: the program or its result uses a builtin or a constant type
  that is still a `postulate` in Agda (hashes, signatures, BLS12-381,
  `Value`, arrays, `expModInteger`, UTF-8 encoding and decoding,
  `serialiseData`; see `Builtin.lagda.md` and `Utils.lagda.md`). A postulate
  has no definition, so the normaliser gets stuck on it and `refl` cannot go
  through. The proposition is still stated as `Pending (evalRaw t ≡ r)` and
  type-checked, which checks that the terms are well-formed. Cases listed in
  `excludedCases` (known failures) are also emitted as pending.
- **Skipped**: the program does not parse or has free variables, or it
  contains a constant that cannot be written as Agda source at all (BLS12-381
  group elements and Miller-loop results).

The summary at the top of the generated `Conformance.lagda.md` gives the
current counts.

### When the two suites disagree

The two suites share the test cases, the CEK machine and the Agda builtin
definitions, but each one has parts the other doesn't. So a case can fail in
one and pass in the other:

- **Passes in `agda-conformance`, pending here.** Postulated builtins are
  bound to their Haskell implementations with `COMPILE GHC` pragmas, so at
  runtime they compute normally, but at type-checking time they don't reduce.
  This is the most common difference, and it is expected rather than a bug.
  Such a case is only checking the Haskell implementation together with the
  Agda CEK machine, not an Agda specification of the builtin. Once a postulate
  is replaced by a definition, mark the builtin as supported in
  `builtinSupported` and regenerate, so that its cases become `refl` proofs.
- **Passes in `agda-conformance`, fails here.** The Agda definition gives the
  wrong answer, but something on the runtime path hides it. For example, a
  `COMPILE` pragma that replaces a defined function or data type with Haskell
  code makes the compiled program run the Haskell code instead of the Agda
  definition. Errors in the runtime term conversion that happen to cancel out
  can hide it too.
- **Fails in `agda-conformance`, passes here.** The bug is on the runtime path
  only: a wrong `COMPILE` pragma or a broken Haskell↔Agda data binding
  (for example the `ByteString` pattern synonyms), a bug in the FFI term
  conversion (`FFI.Untyped`) or the conversion back, a MAlonzo code-generation
  issue, or a costing mismatch. Budgets are only checked by
  `agda-conformance`, so the entries in its `failingBudgetTests` list pass
  here whenever the evaluation result is right.
- **Fails in both.** The Agda semantics (CEK machine or builtin definition)
  disagree with the expected result, which usually means the Agda
  definitions are wrong (or the expected output is).

A test can also fail here because of a bug in this generator or in
`FFI.AgdaUnparse` that prints the wrong Agda term. In that case Agda usually
reports a type error instead of a failed `refl`.
