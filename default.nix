########################################################################
# default.nix -- The top-level nix build file for Plutus apps.
#
# This file defines various attributes that are used for building and
# developing Plutus apps.
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
  # Whether to check that the pinned shas for haskell.nix are correct. We want this to be
  # false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
  # Whether to build our Haskell packages (and their dependencies) with profiling enabled.
, enableHaskellProfiling ? false
}:
let
  inherit (packages) pkgs plutus-apps;
  inherit (plutus-apps) haskell;
in
rec {
  inherit pkgs plutus-apps;

  inherit (plutus-apps) web-ghc;

  inherit (haskell.packages.plutus-pab.components.exes)
    plutus-pab-examples
    plutus-uniswap;

  webCommon = pkgs.callPackage ./web-common { inherit (plutus-apps.lib) gitignore-nix; };
  webCommonPlutus = pkgs.callPackage ./web-common-plutus { inherit (plutus-apps.lib) gitignore-nix; };
  webCommonPlayground = pkgs.callPackage ./web-common-playground { inherit (plutus-apps.lib) gitignore-nix; };

  plutus-playground = pkgs.recurseIntoAttrs rec {
    haddock = plutus-apps.plutus-haddock-combined;

    inherit (pkgs.callPackage ./plutus-playground-client {
      inherit (plutus-apps.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit haskell webCommon webCommonPlutus webCommonPlayground;
    }) client server generate-purescript start-backend;
  };

  plutus-pab = pkgs.recurseIntoAttrs (pkgs.callPackage ./plutus-pab-client {
    inherit (plutus-apps.lib) buildPursPackage buildNodeModules gitignore-nix filterNpm;
    inherit haskell webCommon webCommonPlutus;
  });

  plutus-use-cases = pkgs.recurseIntoAttrs (pkgs.callPackage ./plutus-use-cases {
    inherit haskell;
  });

  tests = import ./nix/tests/default.nix {
    inherit pkgs docs;
    inherit (plutus-apps.lib) gitignore-nix;
    inherit (plutus-apps) fixStylishHaskell fixPurty fixPngOptimization;
    inherit plutus-playground web-ghc plutus-pab;
    src = ./.;
  };

  docs = import ./nix/docs.nix { inherit pkgs plutus-apps; };

  # This builds a vscode devcontainer that can be used with the plutus-starter project (or probably the plutus project itself).
  devcontainer = import ./nix/devcontainer/plutus-devcontainer.nix { inherit pkgs plutus-apps; };

  build-and-push-devcontainer-script = import ./nix/devcontainer/deploy/default.nix { inherit pkgs plutus-apps; };

  # Packages needed for the bitte deployment
  bitte-packages = import ./bitte { inherit plutus-playground docs pkgs; };
}
