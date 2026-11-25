# Guessing-game verification example

This is a current-Plinth port of the on-chain hash-comparison rule from
plutus-apps `Plutus.Contracts.Game.Alonzo`. It deliberately keeps three raw Data
arguments and tests decoding failures as well as success. It does not rebuild
the old off-chain application or its address-diversifying GameParam.

Build `docusaurus-examples:exe:example-ual-game`, then run the resulting executable
as `example-ual-game environment.json` in an output directory. It writes the draft
CIP-57 compiled-interface `plutus.json`, assurance-v2 `assurance.json`, and separate
digest-bound checking contexts. The blueprint contains invocation roles and schema
references; the contexts contain execution bounds and semantics. Compilation emits claims, not
verification evidence.

To stream the same bundle to stdout, run the following from the repository root.
This example uses an illustrative environment manifest.

```sh
cabal run -v0 docusaurus-examples:exe:example-ual-game -- \
  --ndjson --environment doc/docusaurus/static/code/Example/Ual/Blueprint/environment.json
```

Each NDJSON line has a `path`, an `encoding`, and a `content` string. For
`utf8` records, `content` is the exact JSON file text including its final
newline. Parse it as JSON to inspect the document, or encode it as UTF-8 to
reproduce its digest. Generators with binary artifacts use `base16` for those
records. Each record is flushed as it is produced. Check the exit status before
treating the bundle as complete.

To test streaming from the repository root, build Game and pass its executable
to the smoke test. The test runs both output modes in a temporary directory,
compares each artifact byte for byte, and checks the assurance references.

```sh
target=docusaurus-examples:exe:example-ual-game
cabal build "$target" &&
  python3 doc/docusaurus/static/code/Example/Ual/Game/test-stream.py "$(cabal list-bin "$target")"
```

The UAL 1.0 properties use the stable `gameValidator` binding; the display title
is `Guess the secret`. SHA-256 is opaque to the solver, so the quantified claims
state that matching hashes succeed and different hashes fail. They do not assert
that distinct guesses always have different hashes. An integer datum must fail
for every redeemer/context.

PlutusCoreBlaster's `Tests/BlueprintVerify/run_generated.py` runs this generator,
checks all three properties afresh, executes a concrete hash vector, and records
the inputs and tool versions. See that repository's
`Tests/BlueprintVerify/README.md` for the complete commands and trust boundary.
The checked-in JSON files are a generated snapshot with no verification evidence.
Their small `environment.json` is an illustrative placeholder, not a compiler
output or a verified environment. In the VS Code workflow, you can remove all
JSON files from this example: the extension infers the Cabal target, creates its
project manifest, and creates a bootstrap environment reference in its isolated
output directory. `cardano-blaster check ... --refresh-environment` then captures the
actual Lean/module/solver environment for the verification run. The fresh runner produces a
separate evidence-bearing document with `checkingContextHash` after successful
checks. The old UAL 0.5 fixture remains in PlutusCoreBlaster's regression suite.
