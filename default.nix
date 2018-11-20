########################################################################
# default.nix -- The top-level nix build file for plutus.
#
# This file defines an attribute set of packages.
#
# It contains:
#
#   - pkgs -- the nixpkgs set that the build is based on.
#   - haskellPackages.* -- the package set based on stackage
#   - haskellPackages.ghc -- the compiler
#   - localPackages -- just local packages
#
#   - tests -- integration tests and linters suitable for running in a
#              sandboxed build environment
#
# Other files:
#   - shell.nix   - dev environment, used by nix-shell / nix run.
#   - release.nix - the Hydra jobset.
#   - lib.nix     - the localLib common functions.
#   - nix/*       - other nix code modules used by this file.
#
# See also:
#   - TODO: documentation links
#
########################################################################

let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}  # The nixpkgs configuration file

# Use a pinned version nixpkgs.
, pkgs ? localLib.pkgs

# Disable running of tests for all local packages.
, forceDontCheck ? false

# Enable profiling for all haskell packages.
# Profiling slows down performance by 50% so we don't enable it by default.
, enableProfiling ? false

# Enable separation of build/check derivations.
, enableSplitCheck ? true

# Keeps the debug information for all haskell packages.
, enableDebugging ? false

# Build (but don't run) benchmarks for all local packages.
, enableBenchmarks ? true

# Overrides all nix derivations to add build timing information in
# their build output.
, enablePhaseMetrics ? true

# Overrides all nix derivations to add haddock hydra output.
, enableHaddockHydra ? true

# Disables optimization in the build for all local packages.
, fasterBuild ? false

# Forces all warnings as errors
, forceError ? true

}:

with pkgs.lib;

let
  src = localLib.iohkNix.cleanSourceHaskell ./.;
  errorOverlay = import ./nix/overlays/force-error.nix {
    inherit pkgs;
    # TODO: fix plutus-use-cases and plutus-exe warnings
    #filter = localLib.isPlutus;
    filter = let
      pkgList = pkgs.lib.remove "plutus-use-cases" localLib.plutusPkgList;
      in name: builtins.elem name pkgList;
  };
  customOverlays = optional forceError errorOverlay;
  packages = self: ({
    inherit pkgs;

    # This is the stackage LTS plus overrides, plus the plutus
    # packages.
    haskellPackages = self.callPackage localLib.iohkNix.haskellPackages {
      inherit forceDontCheck enableProfiling enablePhaseMetrics
      enableHaddockHydra enableBenchmarks fasterBuild enableDebugging
      enableSplitCheck customOverlays;
        pkgsGenerated = ./pkgs;
        filter = localLib.isPlutus;
        requiredOverlay = ./nix/overlays/required.nix;
        ghc = pkgs.haskell.compiler.ghc843;
    };

    localPackages = localLib.getPackages {
      inherit (self) haskellPackages; filter = localLib.isPlutus;
    };
    tests = {
      shellcheck = pkgs.callPackage localLib.iohkNix.tests.shellcheck { inherit src; };
      hlint = pkgs.callPackage localLib.iohkNix.tests.hlint {
        inherit src;
        projects = localLib.plutusPkgList;
      };
      stylishHaskell = pkgs.callPackage localLib.iohkNix.tests.stylishHaskell {
        inherit (self.haskellPackages) stylish-haskell;
        inherit src;
      };
    };
    plutus-core-spec = pkgs.callPackage ./plutus-core-spec {};
    inherit (pkgs) stack2nix;
  });

in
  # The top-level package set
  pkgs.lib.makeScope pkgs.newScope packages
