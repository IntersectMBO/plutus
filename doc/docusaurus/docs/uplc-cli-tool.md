---
sidebar_position: 28
---

# UPLC CLI Tool

`uplc` is a command-line tool for working with Untyped Plutus Core (UPLC).
It ships with every [Plutus release](https://github.com/IntersectMBO/plutus/releases) and is useful for developers who build, test, or ship Plutus scripts.

You can also build `uplc` from source by cloning the Plutus repository, running `nix develop`, and then running `cabal build uplc`.

`uplc` supports a variety of subcommands.
Run `uplc --help` to see the available subcommands, and `uplc <subcommand> --help` to see the options of a particular subcommand.
Both `uplc --help` and every `uplc <subcommand> --help` end with a short, worked **Examples** section, so the fastest way to remember how a command is invoked is usually to ask it.

## Subcommands at a glance

| Subcommand | What it does |
| --- | --- |
| `evaluate` | Run a UPLC program on the CEK machine and print the result. |
| `debug` | Step through a UPLC program interactively on the CEK machine. |
| `apply` | Apply one script to others, producing `(... ((f g1) g2) ... gn)`. |
| `apply-to-flat-data` / `apply-to-cbor-data` | Apply a script to flat- or CBOR-encoded `Data` arguments. |
| `convert` | Convert a program between formats (textual, flat, hex, blueprint, …). |
| `print` | Parse a program and pretty-print it. |
| `optimise` / `optimize` | Run the UPLC optimisation pipeline. |
| `benchmark` | Benchmark evaluation with [Criterion](https://hackage.haskell.org/package/criterion). |
| `example` | Show built-in example programs (`uplc example -a` lists them). |
| `dump-cost-model` | Dump the cost model parameters. |
| `print-builtin-signatures` | Print the signatures of the built-in functions. |

## Shell completion

`uplc` can generate a completion script for `bash`, `zsh`, or `fish`.
Completion covers subcommand names, option flags, file paths (for `-i`, `-o`, `--eval-apply`, …), and the allowed values of enumerated options such as `--if`/`--of`, `--print-mode`, `--trace-mode`, and `-S`/`--builtin-semantics-variant`.

To enable completion in the **current** shell:

```bash
# bash
source <(uplc --bash-completion-script "$(command -v uplc)")
```

```bash
# zsh
source <(uplc --zsh-completion-script "$(command -v uplc)")
```

```bash
# fish
uplc --fish-completion-script (command -v uplc) | source
```

To install completion **permanently**, write the generated script to the location your shell loads completions from, for example:

```bash
# bash (system-wide; use a user directory if you prefer)
uplc --bash-completion-script "$(command -v uplc)" | sudo tee /etc/bash_completion.d/uplc > /dev/null

# zsh (a directory on your $fpath)
uplc --zsh-completion-script "$(command -v uplc)" > ~/.zsh/completions/_uplc

# fish
uplc --fish-completion-script (command -v uplc) > ~/.config/fish/completions/uplc.fish
```

The same flags work for the `plc` and `pir` tools; just substitute the program name.

## Evaluating scripts

`uplc evaluate` runs a UPLC program on the CEK machine.
As with every subcommand, if `-i` is omitted the program is read from stdin, which makes it easy to use in a pipeline:

```bash
uplc evaluate -i program.uplc
echo '(program 1.1.0 (con integer 42))' | uplc evaluate
```

Scripts as they appear on-chain (in blueprints, wallets, or block explorers) are usually hex-encoded, so pass `--if hex`:

```bash
uplc evaluate --if hex -i script.hex
```

By default evaluation is silent about resource usage. To see how much CPU and memory a program consumes, pick a budget mode:

- `--counting` (`-c`) — run to completion and report the total budget spent.
- `--tallying` (`-t`) — like `--counting`, but also break the cost down per builtin and per AST-node type.
- `--restricting ExCPU:ExMemory` (`-R`) — run within the given budget and fail if it is exceeded, e.g. `--restricting 1000000:5000`.
- `--restricting-enormous` (`-r`) — run within a very large (effectively unlimited) budget and report the total used. Evaluation already uses this enormous budget by default; `-r` additionally prints it.

```bash
uplc evaluate -i program.uplc --tallying
```

To capture `trace` output emitted by the program, use `--trace-mode`, e.g. `--trace-mode Logs`.

## Applying arguments to a script

A validator becomes a runnable program only once its arguments (datum, redeemer, script context, …) have been applied.
`uplc apply` builds that application for you.
Use `apply` when the arguments are themselves UPLC scripts, and `apply-to-flat-data` / `apply-to-cbor-data` when they are encoded `Data` values (the common case for on-chain arguments):

```bash
# arguments are UPLC scripts
uplc apply --if flat Validator.flat Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat

# arguments are CBOR-encoded Data
uplc apply-to-cbor-data --if flat Validator.flat Datum.cbor Redeemer.cbor Context.cbor --of flat -o Script.flat
```

You can then evaluate the fully-applied script with `uplc evaluate`.

## Script optimization

For most users, the most immediately useful subcommand is `optimize` (or `optimise`), which optimizes UPLC programs.
It runs the same UPLC optimization pipeline that the Plinth compiler uses internally: case-of-known-constructor, inlining, common subexpression elimination (CSE), and more.

Basic usage:

```
uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc
```

By default, both input and output files use the textual format.
If `-i` or `-o` is omitted, `uplc` reads from stdin and writes to stdout, so it fits naturally into shell pipelines.

## The optimization report

Running `uplc optimize` prints an _optimization report_ to stderr.
The report lists each pass that ran, in order, and shows the AST size before and after every pass, along with the size delta.
When evaluation is enabled (see below), each row additionally shows the CPU and memory cost at that stage and the deltas against the previous stage.
When `--certify --certifier-report` is used, the same per-pass numbers are also included in the certifier report file.

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
The CPU and memory cost at every stage are then shown alongside AST sizes in the optimization report.
When `--certify --certifier-report` is used, the same per-pass costs are also included in the certifier report file.

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
