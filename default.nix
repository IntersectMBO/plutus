########################################################################
# default.nix -- The top-level nix build file for Marlowe.
#
# This file defines various attributes that are used for building and
# developing Marlowe.
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
  inherit (packages) pkgs marlowe sources;
  inherit (marlowe) haskell;
in
rec {
  inherit pkgs marlowe;

  inherit (marlowe) web-ghc;

  inherit (haskell.packages.marlowe.components.exes) marlowe-pab;

  # TODO This stuff should probably be exposed as an overlay in the plutus-apps if
  # we switch to flakes.
  webCommon = pkgs.callPackage (sources.plutus-apps + "/web-common") { inherit (marlowe.lib) gitignore-nix; };
  webCommonPlutus = pkgs.callPackage (sources.plutus-apps + "/web-common-plutus") { inherit (marlowe.lib) gitignore-nix; };
  webCommonPlayground = pkgs.callPackage (sources.plutus-apps + "/web-common-playground") { inherit (marlowe.lib) gitignore-nix; };
  plutus-pab = pkgs.recurseIntoAttrs (pkgs.callPackage (sources.plutus-apps + "/plutus-pab-client") {
    inherit (marlowe.lib) buildPursPackage buildNodeModules gitignore-nix filterNpm;
    inherit haskell webCommon webCommonPlutus;
  });

  webCommonMarlowe = pkgs.callPackage ./web-common-marlowe { inherit (marlowe.lib) gitignore-nix; };

  marlowe-playground = pkgs.recurseIntoAttrs rec {
    inherit (pkgs.callPackage ./marlowe-playground-client {
      inherit (marlowe.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit haskell webCommon webCommonMarlowe webCommonPlayground;
    }) client server generate-purescript start-backend;
  };

  marlowe-dashboard = pkgs.recurseIntoAttrs rec {
    inherit (pkgs.callPackage ./marlowe-dashboard-client {
      inherit haskell plutus-pab;
      inherit (marlowe.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit webCommon webCommonMarlowe;
    }) client server-setup-invoker marlowe-invoker generated-purescript generate-purescript start-backend;
  };

  marlowe-web = pkgs.callPackage ./marlowe-website { inherit (marlowe.lib) npmlock2nix gitignore-nix; };

  tests = import ./nix/tests/default.nix {
    inherit pkgs docs sources;
    inherit (marlowe.lib) gitignore-nix;
    inherit (marlowe) fixStylishHaskell fixPurty fixPngOptimization;
    inherit marlowe-playground marlowe-dashboard web-ghc plutus-pab marlowe-pab;
    src = ./.;
  };

  docs = import ./nix/docs.nix { inherit pkgs marlowe; };

  # Test data needed by marlowe-actus provided via niv
  inherit (sources) actus-tests;

  # Packages needed for the bitte deployment
  bitte-packages = import ./bitte { inherit marlowe-playground web-ghc marlowe-pab marlowe-dashboard marlowe-web docs pkgs; };
}
