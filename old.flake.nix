# NOTE: This flake is only used for source pinning and has no outputs
{
  description = "plutus flake for pinning sources";

  inputs = {
    # We intentionally import nixpkgs and haskell.nix as non-flakes, to match the
    # flake-free normal build workflow exactly.
    nixpkgs-flakefree = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixpkgs-unstable";
      flake = false;
    };
    nixpkgs = {
      url = "github:NixOS/nixpkgs/34e4df55664c24df350f59adba8c7a042dece61e";
    };
    haskell-nix = {
      url = "github:input-output-hk/haskell.nix";
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
      url = "github:haskell/haskell-language-server?ref=1.7.0.0";
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
  };

  outputs = _: {
    # hydraJobs.x86_64-linux = import ./obsolete.release.nix { system = "x86_64-linux"; };
    hydraJobs.x86_64-darwin = import ./obsolete.release.nix { system = "x86_64-darwin"; };
  };

}
