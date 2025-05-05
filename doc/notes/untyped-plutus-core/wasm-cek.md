The goal is to compile CEK to WASM.

First of all we need to have a WASM-flavored GHC compiler. This is done by
adding a new flake input:

```nix
# flake.nix
{
  inputs = {
    # ... other inputs
    ghc-wasm.url = "gitlab:haskell-wasm/ghc-wasm?host=gitlab.haskell.org";
  };
}
```

This inputs gives us access to several `ghc-wasm` related packages and executables:

```nix
ghc-wasm-pkgs = with inputs.ghc-wasm.packages.${pkgs.system}; [
  binaryen
  wasmtime
  all_9_6
];
```

which we add to the nix shell.

This way we get a bunch of new executables (`wasm32-wasi-cabal`, `wasm32-wasi-ghc`, `wasm32-wasi-ghci`, etc.) that we can use to compile our code to WASM:

```sh
$ wasm32-wasi-cabal --version
cabal-install version 3.14.2.0
compiled using version 3.14.2.0 of the Cabal library 

$ wasm32-wasi-ghc --version
The Glorious Glasgow Haskell Compilation System, version 9.6.7.20250206
```
## WASI Reactor

Now as we have required tools set up, we need to declare a cabal executable that will 
be compiled to so-called WASI reactor:

```cabal
executable cek-wasm-reactor
  main-is:        Main.hs
  hs-source-dirs: untyped-plutus-core/wasm
  other-modules:
  build-depends:
  ghc-options:
    -O -H14m -no-hs-main -optl-mexec-model=reactor
    "-optl-Wl,--export=hs_init"
```
 
### Finding #1 

Adding such executable to the existing cabal project in the Plutus repo is not
working with the `wasm32-wasi-cabal` because it inevitably fails to compile other 
packages like `plutus-benchmark` or `cardano-constitution` that are not of interest
for this task.

I decided to create [a dedicated cabal repo/project](https://github.com/Unisay/cek-wasm) adding `plutus-core` as a dependency.

