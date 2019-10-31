{ system ? builtins.currentSystem, config ? {} }:
let
  sources = import ./nix/sources.nix;

  iohkNix = import sources.iohk-nix { 
    inherit system config; 
    # FIXME: should use the non-json override, but see https://github.com/input-output-hk/iohk-nix/pull/215
    nixpkgsJsonOverride = builtins.toFile "spec.json" (builtins.toJSON { 
      inherit (sources.nixpkgs) rev sha256; 
      url = "https://github.com/NixOS/nixpkgs-channels";
    });
  };

  nixpkgs = iohkNix.nixpkgs;
  pkgs = iohkNix.getPkgs { extraOverlays = [ (import ./nix/overlays/musl.nix) (import ./nix/overlays/pkgs.nix) ]; };
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
