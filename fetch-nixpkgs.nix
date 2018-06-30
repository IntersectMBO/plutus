let
  fetchNixpkgs = rev: sha256unpacked: builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    sha256 = sha256unpacked;
  };
  nixpkgsJson = builtins.fromJSON (builtins.readFile ./nixpkgs-src.json);
  pkgs_path = fetchNixpkgs nixpkgsJson.rev nixpkgsJson.sha256unpacked;
  pkgs = import pkgs_path { config = {}; overlays = []; };
in
pkgs_path
