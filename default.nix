########################################################################
# default.nix -- The top-level nix build file for Plutus.
#
# This file defines various attributes that are used for building and
# developing Plutus.
#
########################################################################

{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; }
  # Overrides for niv
, sourcesOverride ? { }
  # { pkgs plutusMusl plutus }
, packages ? import ./nix { inherit system crossSystem config sourcesOverride rev checkMaterialization; }
  # An explicit git rev to use, passed when we are in Hydra
, rev ? null
  # Whether to check that the pinned shas for haskell.nix are correct. We want this to be
  # false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
}:

let
  inherit (packages) pkgs plutus plutusMusl;
  inherit (pkgs) lib haskell-nix;
  inherit (plutus) haskell iohkNix git-rev set-git-rev agdaPackages;
  inherit (plutus) easyPS sphinxcontrib-haddock nodejs-headers;
in
rec {
  inherit pkgs plutus plutusMusl;

  inherit (plutus) web-ghc;

  inherit (haskell.packages.plutus-scb.components.exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet;

  webCommon = import ./web-common { inherit lib; };

  plutus-playground = {
    tutorial = docs.site;
    haddock = plutus.plutus-haddock-combined;

    client = pkgs.callPackage ./plutus-playground-client {
      inherit (plutus.lib) buildPursPackage;
      inherit set-git-rev haskell webCommon;
    };
  };

  marlowe-playground = {
    tutorial = docs.marlowe-tutorial;

    client = pkgs.callPackage ./marlowe-playground-client {
      inherit (plutus.lib) buildPursPackage;
      inherit set-git-rev haskell webCommon;
    };
  };

  marlowe-symbolic-lambda = plutusMusl.callPackage ./marlowe-symbolic/lambda.nix {
    haskellPackages = haskell.muslPackages;
  };

  marlowe-playground-lambda = plutusMusl.callPackage ./marlowe-playground-server/lambda.nix {
    haskellPackages = haskell.muslPackages;
  };

  plutus-playground-lambda = plutusMusl.callPackage ./plutus-playground-server/lambda.nix {
    haskellPackages = haskell.muslPackages;
  };

  plutus-scb = pkgs.callPackage ./plutus-scb-client {
    inherit (plutus.lib) buildPursPackage;
    inherit set-git-rev haskell webCommon;
  };

  tests = import ./nix/tests/default.nix {
    inherit pkgs iohkNix;
    inherit (plutus) stylish-haskell purty;
    src = ./.;
  };

  docs = import ./nix/docs.nix { inherit pkgs plutus; };

  deployment = pkgs.callPackage ./deployment {
    inherit plutus marlowe-playground plutus-playground marlowe-symbolic-lambda marlowe-playground-lambda plutus-playground-lambda;
  };

  docker = import ./nix/docker.nix {
    inherit (pkgs) dockerTools binutils-unwrapped coreutils bash git cabal-install writeTextFile;
    inherit plutus-playground marlowe-playground haskell;
  };
}
