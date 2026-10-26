
<a id='changelog-1.72.0.0'></a>
# 1.72.0.0 — 2026-10-15

## Added

- `plutus-executables` is now published to CHaP by the release process, so `uplc`, `plc`, `pir` and `plutus` can be installed with `cabal install plutus-executables` instead of being built from a checkout. The package metadata was tidied up for distribution (`description`, `autogen-modules` for `Paths_plutus_executables`, `base` bounds on the test suites).

- Releases now ship prebuilt `uplc`, `plc`, `pir` and `plutus` executables for macOS Apple Silicon, in addition to the static Linux x86_64 binaries. They are built by Hydra and fetched from the cache by the release script.

<a id='changelog-1.70.0.0'></a>
# 1.70.0.0 — 2026-09-22

## Fixed

- `uplc optimise --certify` now exits with a non-zero exit code when certification fails in the `--certifier-basic` and `--certifier-report` output modes, instead of exiting successfully. It also prints whether certification succeeded in every output mode.

<a id='changelog-1.43.0.0'></a>
# 1.43.0.0 — 2025-03-20

## Fixed

- Impossibly long certification of the Marlowe semantics example now takes ~20s
