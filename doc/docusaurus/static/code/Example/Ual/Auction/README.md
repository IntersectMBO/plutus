# Auction with a detached formal specification

`OnChain.hs` applies the existing `AuctionValidator.hs` quick-start validator to
fixed parameters. `FormalSpec.hs` imports the implementation and contains all
UAL annotations. `Main.hs` builds the compiled-interface blueprint and assurance
bundle from the compiled validator and separately compiled `outbids` helper.

`plutus.json` contains one ledger script. `assurance.json` contains the helper's
actual UPLC, its SHA-256 digest, native integer arguments and boolean result,
and all properties. `[kind: script]` is the default; `[kind: function]` routes
an ONCHAIN target to assurance. There is no helper validator in the blueprint.

The formal specification uses typed V3 `ScriptContext` constructors from
`CardanoLedgerApi.Examples.Auction` and encodes them at the raw Data boundary.
The malformed-context property exercises that raw boundary directly. The helper
property checks its exact native return value, not merely successful termination.

The contexts are adapted from input-output-hk/CardanoLedgerApiBlaster's
`main` branch, commit
`9938562fd452351655fe2f6b63e583c62422687c`. They cover the no-previous-bid,
positive-previous-bid and payout transaction shapes with symbolic integers.
The upstream example is [Tests/Scripts/Auction on main](https://github.com/input-output-hk/CardanoLedgerApiBlaster/tree/main/Tests/Scripts/Auction).
`upstream.json` pins that revision and records the SHA-256 of its two Lean files
and CBOR. All three files are byte-identical to the earlier source pin used by
the existing verification run; the difference is the added upstream README.

Current Plinth source is recompiled; this does not assert byte identity with
the upstream CBOR or import the upstream theorem proofs. The detached specification
ports all 26 theorem statements from the pinned upstream audit, alongside the five
interface/scenario claims. The runner also requires both upstream “always fails”
statements to be falsified and evaluates 18 concrete acceptance/rejection witnesses.
These bounded transaction shapes do not establish ledger validity or coverage of
all transactions; the double-satisfaction claim preserves the upstream scenario
and does not prove a complete transaction passes phase-one ledger validation.

Build `docusaurus-examples:exe:example-ual-auction`. In CardanoLedgerApiBlaster,
build and run:

```sh
lake build Blaster:shared CardanoLedgerApi.Examples.Auction PlutusCore.UPLC.BlueprintEncoding.Assurance
lake env python3 Tests/BlueprintVerify/run_auction.py /absolute/path/to/example-ual-auction /absolute/path/to/output
```

Use a Z3 build compatible with that checkout of Blaster (the local newer Blaster
requires `recfun-finder`). Its executable is hashed into the environment manifest.
The runner captures that environment, invokes the generator, verifies every
claim and runs negative checks for byte tampering, scopes, wire encodings and
exhausted steps. `run-report.json` records the results and generator digest.
The full validator uses an explicit 20,000 CEK-step bound; this is not a ledger
cost budget. The JSON snapshots here contain no verification evidence; regenerate the pinned
environment before checking on another machine or after rebuilding dependencies.

The helper shares its Haskell binding with the validator, but its separate proof
is not automatically a proof about compiler inlining/optimization. The
Auction scenario and audit claims independently execute the compiled full validator.

The runner loads Blaster's compiled shared library when it is available on the
Lake search path. An explicit `ASSURANCE_NATIVE_LIBRARY` overrides discovery;
the runner passes that same path to Lean's `--load-dynlib` and records its hash
in the checking environment. Capture and verification must use the same mode.
The manifest also pins the 60-second solver timeout, unlimited Lean heartbeats
and a recursion limit of 100000. The runner bounds each Lean process separately.
