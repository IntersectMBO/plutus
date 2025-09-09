# DevEnv & CI - Maintenance Guide & Troubleshooting

This document is intended both for maintainers of the nix code and for developers facing issues with their development environment or with the CI system. Use CTRL-F to look for relevant keywords.

### 1) `nix develop` fails to enter the shell, `cabal build` fails when it shouldn't.

In general when facing any problem related to the nix shell or cabal failing to build when it shouldn't, the first step is to make sure you are using the latest shell from master: first exit the nix shell, then `git pull --rebase origin master`, then re-enter the nix shell (i.e. run `nix develop`). 

If that fails, you might be facing a caching issue. In that case, try this before exiting and re-entering the nix shell:

`rm -r ~/.cabal/{store,packages} plutus-metatheory/_build dist dist-newstyle`

### 2) `nix develop` is updating the `flake.lock` file.

This should never happen, it is a bug in nix, and has been observed in version `2.26.1`.
Downgrade or upgrade your nix installation to fix this issue. 

### 3) `cabal test all` fails

Sometimes cabal needs a `cabal build all` before it can successfully execute a `cabal test all`.

### 4) How to update `hackage`, `haskell.nix` and `CHaP`

`nix flake update haskell-nix` updates [haskell.nix](https://github.com/input-output-hk/haskell.nix).
This should be done infrequently as it is likely to break the nix code.
If you just want new packages from `hackage` or `CHaP` instead, you can independently run:
`nix flake update hackage CHaP`.
Then you can change the `index-state` in `cabal.project`: you pick an arbitrary date, and if it's too new, `cabal` will error out and suggest the latest known date which you can copy-paste.

### 5) How to change what gets build in CI

Modify `nested-ci-jobs = {..}` in [./nix/outputs.nix](https://github.com/input-output-hk/haskell.nix).

### 6) How to change what gets exposed in the flake outputs

Modify `packages = {..}` in [./nix/outputs.nix](https://github.com/input-output-hk/haskell.nix).

### 7) How to build fully static Haskell executables with Nix

Look at `static-haskell-packages = {..}` in [./nix/outputs.nix](https://github.com/input-output-hk/haskell.nix).

### 8) How to manage cross-compilation on Windows via Wine with Nix

Look at `windows-hydra-jobs = {..}` in [./nix/outputs.nix](https://github.com/input-output-hk/haskell.nix).

### 9) How to define build variants and cabal flags in the nix code

The nix builds can be overridden inside [./nix/project.nix](https://github.com/input-output-hk/haskell.nix).
New cabal flags and configuration options can be defined there.