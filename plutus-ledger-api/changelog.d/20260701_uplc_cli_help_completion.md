### Added

- The `uplc`, `plc`, and `pir` command-line tools are now easier to use:
  - **Shell completion.** The `plutus-execlib` option parsers now carry
    completion metadata, so `uplc`/`plc`/`pir` can complete subcommand names,
    file paths (for `-i`, `-o`, `--eval-apply`, …), and the allowed values of
    enumerated options such as `--if`/`--of`, `--print-mode`, `--trace-mode`,
    and `-S`/`--builtin-semantics-variant`. Enable it with, e.g.,
    `source <(uplc --bash-completion-script "$(command -v uplc)")` (bash; `zsh`
    and `fish` variants are also available).
  - **Worked examples in `--help`.** The top-level help and each subcommand's
    help now end with an `Examples` section. A new
    `PlutusCore.Executable.Help` module in `plutus-execlib` provides the helper
    used to build these footers.
