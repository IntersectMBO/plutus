# `uplc`

`uplc` is the command-line tool for working with **Untyped Plutus Core** (UPLC):
evaluating, debugging, applying arguments, converting between formats,
optimising, and benchmarking programs.

For end-user documentation, including a full walk-through of the optimiser, see
the [UPLC CLI Tool](https://plutus.cardano.intersectmbo.org/docs/uplc-cli-tool)
page on the documentation site.

## Running

During development, run it through `cabal`, which rebuilds as needed:

```bash
cabal run uplc -- <args>
# e.g.
cabal run uplc -- evaluate -i program.uplc
```

A pre-built `uplc` also ships with every
[Plutus release](https://github.com/IntersectMBO/plutus/releases).

## Discovering commands

`uplc` uses subcommands. Ask the tool what it can do:

```bash
uplc --help                 # top-level overview + examples
uplc evaluate --help        # options and examples for one subcommand
```

The top-level help and the help of the most commonly used subcommands end with
a worked **Examples** section.

## Shell completion

`uplc` can emit a completion script for bash, zsh, or fish. To enable it in the
current shell:

```bash
# bash
source <(uplc --bash-completion-script "$(command -v uplc)")
# fish
uplc --fish-completion-script (command -v uplc) | source
```

For zsh the generated script is a completion function body, so it cannot be
sourced directly; install it as `_uplc` on your `$fpath` instead:

```bash
mkdir -p ~/.zsh/completions
uplc --zsh-completion-script "$(command -v uplc)" > ~/.zsh/completions/_uplc
fpath+=(~/.zsh/completions)
autoload -U compinit && compinit
```

Completion covers subcommand names, flags, file paths, and the allowed values of
enumerated options (formats, print modes, builtin-semantics variants, …). The
same flags work for the sibling `plc` and `pir` tools.

## Implementation notes

The three tools `uplc`, `plc`, and `pir` share their option parsers and most of
their plumbing, which lives in the `plutus-execlib` library
(`plutus-ledger-api/executables/src/PlutusCore/Executable/`):

- `Parsers` — the shared `optparse-applicative` option parsers (input/output,
  formats, optimiser flags, …), including the shell-completion metadata.
- `Help` — helpers for the `Examples` footer shown in `--help` output.
- `Common`, `Eval`, `Blueprint`, `OptimizerReport`, `Types`, `AstIO` — the rest
  of the shared machinery.

The `uplc`-specific command wiring is in
[`Main.hs`](./Main.hs).
