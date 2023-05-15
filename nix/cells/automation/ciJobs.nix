{ inputs, cell }:

# TODO(std) Keep an eye on input-output-hk/haskell.nix#1743 for new utility functions.

let


  inherit (inputs.cells.plutus) library;
  inherit (library) pkgs;
  inherit (pkgs.stdenv) system;
  inherit (pkgs) lib;

  make-haskell-jobs = project:
    let
      packages = library.haskell-nix.haskellLib.selectProjectPackages project.hsPkgs;
    in
    rec {
      components = {
        exes = library.haskell-nix.haskellLib.collectComponents' "exes" packages;
        tests = library.haskell-nix.haskellLib.collectComponents' "tests" packages;
        benchmarks = library.haskell-nix.haskellLib.collectComponents' "benchmarks" packages;
        libraries = library.haskell-nix.haskellLib.collectComponents' "library" packages;
        sublibs = library.haskell-nix.haskellLib.collectComponents' "sublibs" packages;
      };

      checks = library.haskell-nix.haskellLib.collectChecks' packages;

      # Build all the haddock for all the components that have it. This ensures that it all
      # builds properly on all the GHC versions we're testing.
      haddock =
        let
          allComponents = lib.collect (x: lib.isDerivation x) components;
          allHaddocks = pkgs.lib.concatMap (x: lib.optional (x ? doc) x.doc) allComponents;
        in
        pkgs.releaseTools.aggregate {
          name = "all-haddock";
          meta.description = "All haddock for all components";
          constituents = allHaddocks;
        };

      roots = project.roots;
      plan-nix = project.plan-nix;
    };

  native-plutus-810-jobs = make-haskell-jobs library.plutus-project-810;
  native-plutus-92-jobs = make-haskell-jobs library.plutus-project-92;
  native-plutus-96-jobs = make-haskell-jobs library.plutus-project-96;

  windows-plutus-92-jobs = make-haskell-jobs library.plutus-project-92.projectCross.mingwW64;

  other-jobs = inputs.cells.plutus.devshells // inputs.cells.plutus.packages;

  jobs =
    # Drop these once we switch to 9.2 by default
    { ghc810 = native-plutus-810-jobs; } //
    { ghc92 = native-plutus-92-jobs; } //
    # 9.6 is busted on darwin because of https://github.com/well-typed/cborg/issues/311
    lib.optionalAttrs (system == "x86_64-linux") { ghc96 = native-plutus-96-jobs; } //
    # Only cross-compile to windows from linux
    lib.optionalAttrs (system == "x86_64-linux") { mingwW64 = windows-plutus-92-jobs; } //
    other-jobs;

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  filtered-jobs = lib.filterAttrsRecursive (n: _: n != "recurseForDerivations") jobs;

  required-job = pkgs.releaseTools.aggregate {
    name = "required-plutus";
    meta.description = "All jobs required to pass CI";
    constituents = lib.collect lib.isDerivation filtered-jobs;
  };

  final-jobset =
    if system == "x86_64-linux" || system == "x86_64-darwin" || system == "aarch64-darwin" then
      filtered-jobs // { required = required-job; }
    else { };

in

final-jobset
