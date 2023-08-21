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

  all-jobs =
    let
      x86_64-linux = {
        ghc810 = make-haskell-jobs library.plutus-project-810;
        ghc92 = make-haskell-jobs library.plutus-project-92;
        ghc96 = make-haskell-jobs library.plutus-project-96;
        devshells = inputs.cells.plutus.devshells;
        packages = inputs.cells.plutus.packages;
        mingwW64 = make-haskell-jobs library.plutus-project-92.projectCross.mingwW64;
      };

      x86_64-darwin =
        # Cross-compiling to windows only works from linux, and we only care about ghc 9.2
        removeAttrs x86_64-linux [ "mingwW64" ];

      # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
      # Se we only build roots and devshells on aarch to avoid overloading the builders.
      aarch64-darwin = {
        ghc810.roots = x86_64-linux.ghc810.roots;
        ghc92.roots = x86_64-linux.ghc92.roots;
        ghc96.roots = x86_64-linux.ghc96.roots;
        # Note: We can't build the 9.6 shell on aarch64-darwin
        # because of https://github.com/well-typed/cborg/issues/311
        devshells = removeAttrs x86_64-linux.devshells [ "plutus-shell-96" ];
      };

      system-matrix = { inherit x86_64-linux x86_64-darwin aarch64-darwin; };
    in
    system-matrix.${system};

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  filtered-jobs = lib.filterAttrsRecursive (n: _: n != "recurseForDerivations") all-jobs;

  # Require everything: there's not much point having a CI job if it isn't required!
  required-job = pkgs.releaseTools.aggregate {
    name = "required-plutus";
    meta.description = "All jobs required to pass CI";
    constituents = lib.collect lib.isDerivation filtered-jobs;
  };

  merged-jobset = filtered-jobs // { required = required-job; };

  is-supported-system = lib.elem system [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" ];

  final-jobset = lib.optionalAttrs is-supported-system merged-jobset;

in

final-jobset
