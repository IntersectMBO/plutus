# NOTE: This flake is only used for source pinning and has no outputs
{
  description = "plutus flake for pinning sources";

  inputs = {
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
      url = "github:input-output-hk/haskell.nix/angerman/fix-ghcjs/";
      flake = false;
    };
    cardano-repo-tool = {
      url = "github:input-output-hk/cardano-repo-tool";
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
    pre-commit-hooks-nix = {
      url = "github:cachix/pre-commit-hooks.nix";
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

  outputs = _: { };
}
