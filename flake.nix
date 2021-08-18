# NOTE: This flake is only provided as interface to `bitte` and shouldn't be used otherwise
#
# Occasionally building flake builds will segfault. The workaround for this is to
# disable the garbage collector  `GC_DONT_GC=1  nix build .#web-ghc-server
#
# In case you are not sure if you should be using this flake, the answer is: No.
{
  description = "plutus flake for pinning sources and bitte deployments";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils?rev=b543720b25df6ffdfcf9227afafc5b8c1fabfae8";

    # We intentionally import nixpkgs and haskell.nix as non-flakes, to match the
    # flake-free normal build workflow exactly.
    nixpkgs = {
      type = "github";

      owner = "NixOS";

      repo = "nixpkgs";

      # We pin this revision to avoid mass-rebuilds from the auto-update process.
      rev = "2457ddc9522b0861649ee5e952fa2e505c1743b7";

      ref = "nixpkgs-unstable";

      flake = false;
    };
    haskell-nix = {
      # We pin this revision to avoid mass-rebuilds from the auto-update process.
      url = "github:input-output-hk/haskell.nix?rev=64c8bc4937fde531bf0c4756df44d37d9a00aa97";

      flake = false;
    };

    actus-tests = {
      url = "github:actusfrf/actus-tests";

      flake = false;
    };
    cardano-repo-tool = {
      url = "github:input-output-hk/cardano-repo-tool";

      flake = false;
    };
    easy-purescript-nix = {
      url = "github:justinwoo/easy-purescript-nix";

      flake = false;
    };
    gitignore-nix = {
      url = "github:hercules-ci/gitignore.nix";

      flake = false;
    };
    hackage-nix = {
      # We pin this revision to avoid unhelpful daily churn from the auto-update process.
      url = "github:input-output-hk/hackage.nix?rev=23545a41ef50c4328e3f95b9a63db59f3ada3518";

      flake = false;
    };
    haskell-language-server = {
      url = "github:haskell/haskell-language-server?ref=1.1.0";

      flake = false;
    };
    iohk-nix = {
      # We pin this revision to avoid unhelpful frequent churn from the auto-update process.
      url = "github:input-output-hk/iohk-nix?rev=cbd497f5844249ef8fe617166337d59f2a6ebe90";

      flake = false;
    };
    npmlock2nix = {
      url = "github:tweag/npmlock2nix";

      flake = false;
    };
    pre-commit-hooks-nix = {
      url = "github:cachix/pre-commit-hooks.nix";

      flake = false;
    };
    spago2nix = {
      url = "github:justinwoo/spago2nix";

      flake = false;
    };
    sphinxcontrib-haddock = {
      url = "github:michaelpj/sphinxcontrib-haddock";

      flake = false;
    };
    stackage-nix = {
      # We pin this revision to avoid unhelpful daily churn from the auto-update process.
      url = "github:input-output-hk/stackage.nix?rev=e32c8b06d56954865725514ce0d98d5d1867e43a";

      flake = false;
    };
  };

  outputs = { self, flake-utils, ... }@inputs:
    (flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        topLevel = import ./. {
          inherit system;
          sources = removeAttrs inputs [ "self" "flake-utils" ];
        };

        inherit (topLevel) pkgs plutus;
      in
      rec {
        packages = rec {
          marlowe-playground-client = topLevel.marlowe-playground.client;
          marlowe-playground-server = topLevel.marlowe-playground.server;

          plutus-playground-client = topLevel.plutus-playground.client;
          plutus-playground-server = topLevel.plutus-playground.server;

          web-ghc-server = topLevel.web-ghc;

          marlowe-pab = topLevel.marlowe-pab;
          marlowe-run-client = topLevel.marlowe-dashboard.client;

          marlowe-website = topLevel.marlowe-web;

          plutus-docs = topLevel.docs.site;
        };
      }));
}
