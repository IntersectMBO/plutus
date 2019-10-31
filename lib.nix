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
      }) { inherit system config; nixpkgsJsonOverride = ./nixpkgs.json; };

  # nixpkgs can be overridden for debugging purposes by setting
  # NIX_PATH=custom_nixpkgs=/path/to/nixpkgs
  pkgs = iohkNix.getPkgs { extraOverlays = [ (import ./nix/overlays/musl.nix) (import ./nix/overlays/pkgs.nix) ]; };
  nixpkgs = iohkNix.nixpkgs;
  lib = pkgs.lib;
  getPackages = iohkNix.getPackages;

  # List of all public (i.e. published Haddock, will go on Hackage) Plutus pkgs
  plutusPublicPkgList = [
    "language-plutus-core"
    "plutus-contract"
    "plutus-core-interpreter"
    "plutus-playground-lib"
    "plutus-exe"
    "plutus-ir"
    "plutus-tx"
    "plutus-wallet-api"
    "plutus-emulator"
    "iots-export"
  ];

  isPublicPlutus = name: builtins.elem name plutusPublicPkgList;

  # List of all Plutus packges in this repository.
  plutusPkgList = plutusPublicPkgList ++ [
    "plutus-playground-server"
    "plutus-tutorial"
    "plutus-book"
    "plutus-use-cases"
    "playground-common"
    "marlowe"
    "marlowe-playground-server"
    "deployment-server"
    "marlowe-symbolic"
  ];

  isPlutus = name: builtins.elem name plutusPkgList;

  regeneratePackages = iohkNix.stack2nix.regeneratePackages { hackageSnapshot = "2019-09-12T00:02:45Z"; };

  unfreePredicate = pkg: 
      if pkg ? name then (builtins.parseDrvName pkg.name).name == "kindlegen" 
      else if pkg ? pname then pkg.pname == "kindlegen" else false;

  comp = f: g: (v: f(g v));

in lib // {
  inherit
  getPackages
  iohkNix
  isPlutus
  isPublicPlutus
  plutusPublicPkgList
  plutusPkgList
  regeneratePackages
  unfreePredicate
  nixpkgs
  pkgs
  comp;
}
