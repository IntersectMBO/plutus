{ inputs, cell }:

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

  plutus-project-with-coverage = plutus-project.appendModule { coverage = true; };

  native-plutus-jobs = make-haskell-jobs plutus-project;

  windows-plutus-jobs = make-haskell-jobs plutus-project.projectCross.mingwW64;

  other-jobs = {
    plutus.shells = inputs.cells.plutus.devshells;
    doc.shells = inputs.cells.doc.devshells;
    doc.packages = inputs.cells.doc.packages;
    doc.scripts = inputs.cells.doc.scripts;
    toolchain.packages = inputs.cells.toolchain.packages;
  };

  jobs =
    if system == "x86_64-linux" then {
      plutus.windows = windows-plutus-jobs;
      plutus.native = native-plutus-jobs;
      other = other-jobs;
      coverage = plutus-project-with-coverage.projectCoverageReport;
    } else if system == "x86_64-darwin" then {
      plutus.native = native-plutus-jobs;
      other = other-jobs;
    } else { };

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
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
