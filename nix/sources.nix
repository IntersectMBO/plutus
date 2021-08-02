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
      (fetcher-args lock.nodes.${inputs.nixpkgs}.locked))
    {
      inherit system;
    };
in
builtins.mapAttrs
  (_: node-name: pkgs.fetchzip (fetcher-args lock.nodes.${node-name}.locked))
  inputs
