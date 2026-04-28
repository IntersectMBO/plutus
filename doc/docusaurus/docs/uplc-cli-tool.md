---
sidebar_position: 28
---

# UPLC CLI Tool

`uplc` is a command-line tool for working with Untyped Plutus Core (UPLC).
It ships with every [Plutus release](https://github.com/IntersectMBO/plutus/releases) and is useful for developers who build, test, or ship Plutus scripts.

You can also build `uplc` from source by cloning the Plutus repository, running `nix develop`, and then running `cabal build uplc`.

`uplc` supports a variety of subcommands.
Run `uplc --help` to see the available subcommands, and `uplc <subcommand> --help` to see the options of a particular subcommand.

# Script optimization

For most users, the most immediately useful subcommand is `optimize` (or `optimise`), which optimizes UPLC programs.
It runs the same UPLC optimization pipeline that the Plinth compiler uses internally: case-of-known-constructor, inlining, common subexpression elimination (CSE), and more.

Basic usage:

```
uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc
```

By default, both input and output files use the textual format.
If `-i` or `-o` is omitted, `uplc` reads from stdin and writes to stdout, so it fits naturally into shell pipelines.

## Input and output formats

`uplc` has always supported textual and flat-encoded scripts, but two recent additions make it much easier to plug into existing toolchains:

__Hex-encoded scripts__.
This is the format most off-chain tools, wallets, and block explorers use.
To use hex input or output, specify the formats with `--if` and `--of`:

```
uplc optimize --if hex --of hex -i MyValidator.uplc -o MyValidator-opt.uplc
```

__Blueprint JSON__.
A [CIP-57](https://cips.cardano.org/cips/cip57/) blueprint is the standard packaging format for Plutus contracts and may contain multiple validators.
You can feed a blueprint straight into `uplc` and get an optimized blueprint back, with every validator optimized and the corresponding hash field recomputed:

```
uplc optimize --if blueprint --of blueprint -i MyBlueprint.json -o MyBlueprint.opt.json
```

The full list of supported formats is:

- `textual` — human-readable UPLC syntax
- `flat` / `flat-deBruijn` — flat-encoded with de Bruijn indices
- `flat-named` — flat-encoded with textual names
- `flat-namedDeBruijn` — flat-encoded with named de Bruijn indices
- `serialised` — CBOR-wrapped flat with de Bruijn indices
- `hex` — `serialised` plus hex encoding (what blueprints and most tools use)
- `blueprint` — blueprint JSON

## Configuring the optimization pipeline

The `opt-*` flags let you configure the optimization pipeline.
Run `uplc optimize --help` to see the full list.

The flags most worth experimenting with when you're optimizing primarily for either execution cost or script size are the inliner-aggressiveness flags — `--opt-inline-unconditional-growth` and `--opt-inline-callsite-growth` — plus `--opt-no-inline-constants` and `--opt-cse-which-subterms`.
They give you direct control over the cost-vs-size tradeoff.

The two `--opt-inline-...-growth` flags govern how much AST growth the inliner accepts.
Higher values mean more aggressive inlining, and more inlining usually reduces cost, but sometimes increases size.
`--opt-no-inline-constants` controls the inlining of constants specifically: inlining constants is good for cost, but if a large constant occurs at many callsites, inlining it copies the constant each time and inflates size.
`--opt-cse-which-subterms` controls how aggressive common subexpression elimination is: `all` is more aggressive than the default `exclude-work-free`.
Aggressive CSE typically reduces size (more duplicates get factored out) but can raise cost (each factored subterm adds a small evaluation overhead).

## Certifying optimizations

`uplc` includes certifiers for optimization passes.
Each pass is formalized in Agda as a translation relation between pre- and post-terms together with a procedure that decides whether the relation holds.

Each certifier takes the pre- and post-terms of a single pass and either accepts the transformation as valid or rejects it.
The `--certify` flag runs the certifier, and can produce an Agda artifact that can be checked independently by Agda.

> :pushpin: **NOTE**
>
>Certification is currently experimental.

Basic usage:

```
uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc --certify MyProof
```

This produces an Agda project (the default output mode) that encodes a correctness proof of the transformation, named after the `MyProof` argument.
You can then run the Agda type checker on the generated project to verify the certificate.

The certifier has three output modes:

- `--certifier-project` — emit a full Agda project that can be type-checked with Agda.
  This is the default.
- `--certifier-report REPORT_FILE` — emit a human-readable report to the given file.
  The report summarizes the optimization passes that ran, and includes the AST size at each stage.
  It can also include the execution cost at each stage when evaluation is enabled (explained below).
- `--certifier-basic` — emit minimal output.

For blueprints, the certifier runs once per validator.
Report filenames and project directories have the validator's title appended automatically.

## Evaluating before and after each optimization

The `--eval*` flags supply arguments to the script and run it on the CEK machine at every stage of the optimization pipeline, recording the execution cost at each step.

> :pushpin: **NOTE**
>
> The `--eval*` flags currently only have effect when used with `--certify`, and the costs are only recorded in the certifier report when the certifier output mode is `--certifier-report`. Supporting evaluation independently of certification is planned future work.

For a single script:

```
uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc \
  --certify MyProof --certifier-report MyValidator.report \
  --eval-apply datum.hex \
  --eval-apply redeemer.hex \
  --eval-apply context.hex
```

By default `--eval-apply` arguments are interpreted as hex-encoded `Data`.
If you want to supply a UPLC program instead, use `--eval-arg-kind prog`.
To evaluate a script without supplying any arguments, use `--eval`.

For blueprints, since a blueprint may contain multiple validators, use `--eval-args-dir DIR` to point at a directory with the following layout:

```
args/
├── MyMintingPolicy/
│   ├── 0        # first argument to MyMintingPolicy
│   └── 1        # second argument
└── MySpendingValidator/
    ├── 0
    ├── 1
    └── 2
```

Then run:

```
uplc optimize --if blueprint --of blueprint -i MyBlueprint.json -o MyBlueprint-opt.json \
  --certify MyProof --certifier-report MyProof.report \
  --eval-args-dir args
```

Each validator is evaluated with the arguments under the corresponding subdirectory.
The result is an optimized blueprint, and a per-validator report showing how the execution budget changed at each optimization step.
