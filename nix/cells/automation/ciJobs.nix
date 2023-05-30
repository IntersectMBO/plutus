{ inputs, cell }:

# TODO(std) Keep an eye on input-output-hk/haskell.nix#1743 for new utility functions.

let


  inherit (inputs.cells.plutus) library;
  inherit (library) pkgs;
  inherit (pkgs.stdenv) system;
  inherit (pkgs) lib;

  x86linux = "x86_64-linux";
  x86darwin = "x86_64-darwin";
  aarchdarwin = "aarch64-darwin";
  supportedSystems = [ x86linux x86darwin aarchdarwin ];

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

  windows-plutus-810-jobs = make-haskell-jobs library.plutus-project-810.projectCross.mingwW64;

  devshells =
    # Note: We can't build the 9.6 shell on aarch64-darwin
    # because of https://github.com/well-typed/cborg/issues/311
    let s = inputs.cells.plutus.devshells;
    in
    if system == aarchdarwin
    then builtins.removeAttrs s [ "plutus-shell-96" ]
    else s;

  # this just has all the package roots in, which we're going to want
  # to be extra sure we always build
  roots = {
    ghc810 = native-plutus-810-jobs.roots;
    ghc92 = native-plutus-92-jobs.roots;
    ghc96 = native-plutus-96-jobs.roots;
  };

  jobs =
    # Only build all the main packages on linux and _one_ dawin platform, to avoid doing too
    # much work in CI. Plausibly if things build on x86 darwin then they'll build on aarch
    # darwin, and it avoids overloading the builders.
    lib.optionalAttrs (system == x86linux || system == x86darwin)
      (
        { ghc810 = native-plutus-810-jobs; }
        //
        { ghc92 = native-plutus-92-jobs; }
        //
        { ghc96 = native-plutus-96-jobs; }
        //
        { mingwW64 = windows-plutus-92-jobs; }
        //
        inputs.cells.plutus.packages
      )
    //
    # Build devshells on all platforms so people can work effectively
    devshells
    //
    # Build roots on all platforms so stuff doesn't get GCd
    roots;

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  filtered-jobs = lib.filterAttrsRecursive (n: _: n != "recurseForDerivations") jobs;

  required-job = pkgs.releaseTools.aggregate {
    name = "required-plutus";
    meta.description = "All jobs required to pass CI";
    # require everything: there's not much point having a CI job if it isn't required!
    constituents = lib.collect lib.isDerivation filtered-jobs;
  };

  final-jobset =
    if builtins.elem system supportedSystems
    then filtered-jobs // { required = required-job; }
    else { };

in

final-jobset
