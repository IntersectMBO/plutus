# TODO(std) replace all occurrences of hydra with cicero once hydra is gone.
# Normally we'd name this file default.nix and put it into a hydraJobs folder.
# However that causes all hydra job names to contain an extra string (the flake fragment name)
# in the final attribute path. To make job names shorter we name this file hydraJobs.nix instead.

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
    {
      exes = library.haskell-nix.haskellLib.collectComponents' "exes" packages;
      tests = library.haskell-nix.haskellLib.collectComponents' "tests" packages;
      benchmarks = library.haskell-nix.haskellLib.collectComponents' "benchmarks" packages;
      libraries = library.haskell-nix.haskellLib.collectComponents' "library" packages;
      checks = library.haskell-nix.haskellLib.collectChecks' packages;
      roots = project.roots;
      plan-nix = project.plan-nix;
    };

  native-plutus-8107-jobs = make-haskell-jobs library.plutus-project-8107;
  native-plutus-924-jobs = make-haskell-jobs library.plutus-project-924;

  windows-plutus-924-jobs = make-haskell-jobs library.plutus-project-924.projectCross.mingwW64;

  other-jobs = inputs.cells.plutus.devshells // inputs.cells.plutus.packages;

  jobs =
    # Drop these once we switch to 9.2.4 by default
    { ghc8107 = native-plutus-8107-jobs; } //
    { ghc924 = native-plutus-924-jobs; } //
    # Only cross-compile to windows from linux
    lib.optionalAttrs (system == "x86_64-linux") { mingwW64 = windows-plutus-924-jobs; } //
    other-jobs;

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  # TODO(std) hydra will be gone by the end of month. Remove this stuff when that happens.
  filtered-jobs = lib.filterAttrsRecursive (n: _: n != "recurseForDerivations") jobs;

  required-job = pkgs.releaseTools.aggregate {
    name = "required-plutus";
    meta.description = "All jobs required to pass CI";
    constituents = lib.collect lib.isDerivation filtered-jobs;
  };

  final-jobset =
    if system == "x86_64-linux" || system == "x86_64-darwin" then
      filtered-jobs // { required = required-job; }
    else { };

in

final-jobset
