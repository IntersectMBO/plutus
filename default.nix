########################################################################
# default.nix -- The top-level nix build file for Plutus.
#
# This file defines various attributes that are used for building and
# developing Plutus.
#
########################################################################
{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, sourcesOverride ? { }
, sources ? import ./nix/sources.nix { inherit system; } // sourcesOverride
, haskellNix ? import sources.haskell-nix {
    pkgs = import sources.nixpkgs { inherit system; };
    sourcesOverride = {
      hackage = sources.hackage-nix;
      stackage = sources.stackage-nix;
    };
  }
, packages ? import ./nix { inherit system sources crossSystem config sourcesOverride haskellNix checkMaterialization enableHaskellProfiling; }
  # An explicit git rev to use, passed when we are in Hydra
  # Whether to check that the pinned shas for haskell.nix are correct. We want this to be
  # false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
  # Whether to build our Haskell packages (and their dependencies) with profiling enabled.
, enableHaskellProfiling ? false
}:
let
  inherit (packages) pkgs plutus;
  inherit (plutus) haskell;
in
rec {
  inherit pkgs plutus;

  tests = import ./nix/tests/default.nix {
    inherit pkgs docs;
    inherit (plutus.lib) gitignore-nix;
    inherit (plutus) fixStylishHaskell fixPngOptimization;
    src = ./.;
  };

  docs = import ./nix/docs.nix { inherit pkgs plutus; };
}
