{ inputs, cell }:

let
  inherit (inputs.cells.toolchain.library) pkgs haskell-nix;
  inherit (pkgs.stdenv) hostPlatform;
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

  other-jobs = {
    plutus.shells = inputs.cells.plutus.devshells;
    doc.shells = inputs.cells.doc.devshells;
    doc.packages = inputs.cells.doc.packages;
    doc.scripts = inputs.cells.doc.scripts;
    toolchain.packages = inputs.cells.toolchain.packages;
    toolchain.scripts = inputs.cells.toolchain.scripts;
  };

  constituents = {
    linux = lib.optionalAttrs (hostPlatform.isLinux && hostPlatform.isx86_64) {
      native = native-plutus-jobs;
      windows = windows-plutus-jobs;
      other = other-jobs;
    };
    darwin = lib.optionalAttrs (hostPlatform.isDarwin && hostPlatform.isx86_64) {
      native = native-plutus-jobs;
      other = other-jobs;
    };
  };

in

pkgs.releaseTools.aggregate {
  name = "required-plutus";
  meta.description = "All jobs required to pass CI";
  constituents = lib.collect lib.isDerivation constituents;
}

