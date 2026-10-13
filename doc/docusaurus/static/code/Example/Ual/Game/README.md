# Guessing-game verification example

This is a current-Plinth port of the on-chain hash-comparison rule from
plutus-apps `Plutus.Contracts.Game.Alonzo`. It deliberately keeps three raw Data
arguments and tests decoding failures as well as success. It does not rebuild
the old off-chain application or its address-diversifying GameParam.

Build `docusaurus-examples:exe:example-ual-game`, then run the resulting executable
as `example-ual-game environment.json` in an output directory. The environment
manifest is captured by PlutusCoreBlaster before generation. It writes the draft
CIP-57 compiled-interface `plutus.json`, assurance-v2 `assurance.json`, and separate
digest-bound checking contexts. The blueprint contains invocation roles and schema
references; the contexts contain execution bounds and semantics. Compilation emits claims, not
verification evidence.

The UAL 0.6-draft properties use the stable `gameValidator` binding; the display title
is `Guess the secret`. SHA-256 is opaque to the solver, so the quantified claims
state that matching hashes succeed and different hashes fail. They do not assert
that distinct guesses always have different hashes. An integer datum must fail
for every redeemer/context.

PlutusCoreBlaster's `Tests/BlueprintVerify/run_generated.py` runs this generator,
checks all three properties afresh, executes a concrete hash vector, and records
the inputs and tool versions. See that repository's
`Tests/BlueprintVerify/README.md` for the complete commands and trust boundary.
The checked-in JSON files are a generated snapshot with no verification evidence.
Their environment manifest pins a particular local Lean/module/solver build;
regenerate it for a different checking environment. The fresh runner produces a
separate evidence-bearing document with `checkingContextHash` after successful
checks. The old UAL 0.5 fixture remains in PlutusCoreBlaster's regression suite.
