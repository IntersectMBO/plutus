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

Look at [./nix/static-executables.nix](./static-executables.nix): it builds `uplc`, `plc`, `pir` and `plutus` as musl static binaries on Linux (via haskell.nix's `projectCross`) and, on macOS, with every C library except libSystem linked statically from `pkgsStatic`, exposed as `packages.<system>.static-<exe>`, plus `packages.<system>.release-executables` with the files attached to GitHub releases (Hydra builds it, the release script fetches it from the cache).

### 8) How to manage cross-compilation on Windows via Wine with Nix

Look at `windows-hydra-jobs = {..}` in [./nix/outputs.nix](https://github.com/input-output-hk/haskell.nix).

### 9) How to define build variants and cabal flags in the nix code

The nix builds can be overridden inside [./nix/project.nix](https://github.com/input-output-hk/haskell.nix).
New cabal flags and configuration options can be defined there.

### 10) Windows Template Haskell intermittently fails with `ghc-iserv terminated (1)`

With GHC 9.6.7 and MinGW, an accompanying `scavenge_stack: weird activation record`
error can be caused by incorrect `R_X86_64_PC64` relocations in GHC's runtime linker.
GNU PE/COFF PC64 relocations are relative to the end of the eight-byte relocation field,
but GHC omitted the eight-byte adjustment. This points large stack-frame bitmaps
eight bytes past their intended address; failure depends on whether garbage
collection encounters the affected frame. Retrying can therefore appear to fix it.
The cost-model JSON splice exposes the bug rather than causing it.

`project.nix` enables `-fbyte-code-and-object-code` and `-fprefer-byte-code` only
for the Windows `plutus-core` library. Template Haskell then uses bytecode for
home-package modules instead of loading their native objects through the faulty
linker. The library still produces native object code for normal linking.
These [GHC options](https://downloads.haskell.org/ghc/9.6.7/docs/users_guide/phases.html#ghc-flag--fprefer-byte-code)
also retain simplified Core in interfaces, allowing incremental builds to use bytecode.

This is a scoped workaround, not a fix to GHC's runtime linker. It reuses the
existing compiler and interpreter without rebuilding GHC or changing non-Windows
build options. Remove it once the selected compiler includes the linker correction.

Run the affected Hydra target on x86_64 Linux:

```sh
nix build '.#hydraJobs.x86_64-linux."ghc96-mingsW64:packages:plutus-core:lib:plutus-core"'
```

Validation with the unpatched interpreter also covered fresh and incremental
builds under GC stress (`+RTS -A16k -DS -RTS`, using an interpreter linked with
`-rtsopts`). Preferring native objects instead reproduced `ghc-iserv terminated (1)`.
