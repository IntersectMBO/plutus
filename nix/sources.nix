# This file presents a niv-like interface over the sources listed
# in a flake.lock.
{ system }:
let
  lock = builtins.fromJSON (builtins.readFile ../flake.lock);

  inherit (lock.nodes.${lock.root}) inputs;

  fetcher-args = input:
    if input.type == "github" then {
      name = "source";

      url = "https://github.com/${input.owner}/${input.repo}/archive/${input.rev}.tar.gz";

      sha256 = input.narHash;
    } else throw "non-GitHub flake inputs not yet supported by niv shim";

  # We need to fetch nixpkgs with the builtin tarball fetcher so that
  # we can use the fetcher defined in nixpkgs for all other fetching.
  pkgs = import
    (builtins.fetchTarball
      (fetcher-args lock.nodes.${inputs.__old__nixpkgs}.locked))
    {
      inherit system;
    };

  tmpSources = builtins.mapAttrs
    (_: node-name: pkgs.fetchzip (fetcher-args lock.nodes.${node-name}.locked))
    inputs;

  finalSources = {
    nixpkgs = tmpSources.__old__nixpkgs;
    haskell-nix = tmpSources.__old__haskell-nix;
    cardano-repo-tool = tmpSources.__old__cardano-repo-tool;
    gitignore-nix = tmpSources.__old__gitignore-nix;
    hackage-nix = tmpSources.__old__hackage-nix;
    iohk-nix = tmpSources.__old__iohk-nix;
    pre-commit-hooks-nix = tmpSources.__old__pre-commit-hooks-nix;
    inherit (tmpSources) haskell-language-server sphinxcontrib-haddock;
  };
in
finalSources
