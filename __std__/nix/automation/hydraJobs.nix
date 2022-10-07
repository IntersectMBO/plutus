# Normally we'd name this file default.nix and put it into a hydraJobs folder.
# However this causes all hydra job names to contain an extra string (the flake fragment name)
# in the final attribute path.

{ inputs, cell }:

# TODO(std) Keep an eye on input-output-hk/haskell.nix#1743 for new utility functions.

let
  inherit (inputs.cells.toolchain.library) pkgs haskell-nix;
  inherit (pkgs.stdenv) system;
  inherit (pkgs) lib;

  make-haskell-jobs = project:
    let
      packages = haskell-nix.haskellLib.selectProjectPackages project.hsPkgs;
    in
    {
      exes = haskell-nix.haskellLib.collectComponents' "exes" packages;
      tests = haskell-nix.haskellLib.collectComponents' "tests" packages;
      benchmarks = haskell-nix.haskellLib.collectComponents' "benchmarks" packages;
      libraries = haskell-nix.haskellLib.collectComponents' "library" packages;
      checks = haskell-nix.haskellLib.collectChecks' packages;
      roots = project.roots;
      plan-nix = project.plan-nix;
    };

  plutus-project = inputs.cells.plutus.library.plutus-project;

  native-plutus-jobs = make-haskell-jobs plutus-project;

  windows-plutus-jobs = make-haskell-jobs plutus-project.projectCross.mingwW64;

  other-jobs =
    inputs.cells.plutus.devshells //
    inputs.cells.doc.devshells //
    inputs.cells.doc.packages //
    inputs.cells.doc.scripts //
    inputs.cells.toolchain.packages;

  jobs =
    if system == "x86_64-linux" then
      { native = native-plutus-jobs; windows = windows-plutus-jobs; } // other-jobs
    else if system == "x86_64-darwin" then
      { native = native-plutus-jobs; } // other-jobs
    else
      { };

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  # filtered-jobs = lib.filterAttrsRecursive (n: _: n != "recurseForDerivations") jobs;

  required-job = pkgs.releaseTools.aggregate {
    name = "required-plutus";
    meta.description = "All jobs required to pass CI";
    constituents = lib.collect lib.isDerivation jobs;
  };

  final-jobset =
    if system == "x86_64-linux" || system == "x86_64-darwin" then
      jobs // { required = required-job; }
    else { };

in

final-jobset
