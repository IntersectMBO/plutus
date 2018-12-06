{ system ? builtins.currentSystem, config ? {} }:
let
  # iohk-nix can be overridden for debugging purposes by setting
  # NIX_PATH=iohk_nix=/path/to/iohk-nix
  iohkNix = import (
    let try = builtins.tryEval <iohk_nix>;
    in if try.success
    then builtins.trace "using host <iohk_nix>" try.value
    else
      let
        spec = builtins.fromJSON (builtins.readFile ./iohk-nix.json);
      in builtins.fetchTarball {
        url = "${spec.url}/archive/${spec.rev}.tar.gz";
        inherit (spec) sha256;
      }) { inherit config system; };

  # nixpkgs can be overridden for debugging purposes by setting
  # NIX_PATH=custom_nixpkgs=/path/to/nixpkgs
  pkgs = iohkNix.pkgs;
  nixpkgs = iohkNix.nixpkgs;
  lib = pkgs.lib;
  getPackages = iohkNix.getPackages;

  # List of all plutus pkgs. This is used for `isPlutus` filter and `mapTestOn`
  plutusPkgList = [
    "language-plutus-core"
    "plutus-core-interpreter"
    "plutus-playground-server"
    "plutus-playground-lib"
    "plutus-playground-client"
    "plutus-server-invoker"
    "plutus-exe"
    "plutus-ir"
    "plutus-tx"
    "plutus-tx-plugin"
    "plutus-use-cases"
    "wallet-api"
  ];

  plutusHaskellPkgList = lib.filter (v: v != "plutus-playground-client" && v != "plutus-server-invoker") plutusPkgList;

  isPlutus = name: builtins.elem name plutusPkgList;

  withDevTools = env: env.overrideAttrs (attrs: { nativeBuildInputs = attrs.nativeBuildInputs ++ [ pkgs.cabal-install pkgs.haskellPackages.ghcid ]; });
  comp = f: g: (v: f(g v));
in lib // {
  inherit getPackages iohkNix isPlutus plutusHaskellPkgList plutusPkgList withDevTools pkgs nixpkgs comp;
}
