{ system ? builtins.currentSystem, config ? {} }:
let
  sources = import ./nix/sources.nix;

  iohkNix = import sources.iohk-nix {
    inherit system config;
    # FIXME: should be 'nixpkgsOverride = sources.nixpkgs', but see https://github.com/input-output-hk/iohk-nix/pull/215
    nixpkgsJsonOverride = ./nixpkgs.json;
  };

  nixpkgs = iohkNix.nixpkgs;
  pkgs = iohkNix.getPkgs { extraOverlays = [ (import ./nix/overlays/musl.nix) (import ./nix/overlays/nixpkgs-overrides.nix) ]; };
  lib = pkgs.lib;
  getPackages = { haskellPackages, filter , f ? null }:
    let filtered = lib.filterAttrs (name: drv: filter name) haskellPackages;
    in if f == null then filtered else lib.mapAttrs f filtered;

  # List of all public (i.e. published Haddock, will go on Hackage) Plutus pkgs
  plutusPublicPkgList = [
    "language-plutus-core"
    "plutus-contract"
    "plutus-contract-tasty"
    "plutus-playground-lib"
    "plutus-exe"
    "plutus-ir"
    "plutus-tx"
    "plutus-tx-plugin"
    "plutus-wallet-api"
    "plutus-emulator"
    "plutus-scb"
    "iots-export"
    "marlowe-hspec"
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

  # The Hackage index-state we use for things
  index-state = "2020-02-20T00:00:00Z";

  unfreePredicate = pkg:
      let unfreePkgs = [ "kindlegen" ]; in
      if pkg ? name then builtins.elem (builtins.parseDrvName pkg.name).name unfreePkgs
      else if pkg ? pname then builtins.elem pkg.pname unfreePkgs
      else false;

  comp = f: g: (v: f(g v));

in lib // {
  inherit
  getPackages
  iohkNix
  isPlutus
  isPublicPlutus
  plutusPublicPkgList
  plutusPkgList
  index-state
  unfreePredicate
  nixpkgs
  pkgs
  comp;
}
