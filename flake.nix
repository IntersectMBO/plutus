# NOTE: This flake is only provided as interface to `bitte` and shouldn't be used otherwise
#
# Occasionally building flake builds will segfault. The workaround for this is to
# disable the garbage collector  `GC_DONT_GC=1  nix build .#web-ghc-server
#
# In case you are not sure if you should be using this flake, the answer is: No.
{
  description = "plutus flake for pinning sources and bitte deployments";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";

    # We intentionally import nixpkgs and haskell.nix as non-flakes, to match the
    # flake-free normal build workflow exactly.
    nixpkgs = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixpkgs-unstable";
      flake = false;
    };
    haskell-nix = {
      url = "github:input-output-hk/haskell.nix";
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
      url = "github:input-output-hk/hackage.nix";
      flake = false;
    };
    haskell-language-server = {
      # Pinned to a release
      url = "github:haskell/haskell-language-server?ref=1.3.0";
      flake = false;
    };
    iohk-nix = {
      url = "github:input-output-hk/iohk-nix";
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
      url = "github:input-output-hk/stackage.nix";
      flake = false;
    };
  };

  outputs = { self, flake-utils, ... }@inputs:
    (flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        topLevel = import ./. {
          inherit system;
          sources = inputs;
        };
      in
      {
        packages = topLevel.bitte-packages;
      }));
}
