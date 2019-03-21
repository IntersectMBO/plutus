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
    "plutus-tutorial"
    "plutus-use-cases"
    "interpreter"
    "marlowe"
    "meadow"
    "wallet-api"
  ];

  plutusHaskellPkgList = lib.filter (v: v != "plutus-playground-client" && v != "plutus-server-invoker") plutusPkgList;

  isPlutus = name: builtins.elem name plutusPkgList;

  regeneratePackages = iohkNix.stack2nix.regeneratePackages { hackageSnapshot = "2019-02-28T09:58:14Z"; };

  fixStylishHaskell = pkgs.writeScript "fix-stylish-haskell" ''
    ${pkgs.git}/bin/git diff > pre-stylish.diff
    ${pkgs.fd}/bin/fd \
      --extension hs \
      --exclude '*/dist/*' \
      --exclude '*/docs/*' \
      --exec ${pkgs.haskellPackages.stylish-haskell}/bin/stylish-haskell -i {}
    ${pkgs.git}/bin/git diff > post-stylish.diff
    diff pre-stylish.diff post-stylish.diff > /dev/null
    if [ $? != 0 ]
    then
      echo "Changes by stylish have been made. Please commit them."
    else
      echo "No stylish changes were made."
    fi
    rm pre-stylish.diff post-stylish.diff
    exit
  '';

  comp = f: g: (v: f(g v));
in lib // {
  inherit 
  getPackages 
  iohkNix 
  isPlutus 
  plutusHaskellPkgList 
  plutusPkgList 
  regeneratePackages 
  fixStylishHaskell
  nixpkgs 
  pkgs
  comp;
}
