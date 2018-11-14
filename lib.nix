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
      });

  # nixpkgs can be overridden for debugging purposes by setting
  # NIX_PATH=custom_nixpkgs=/path/to/nixpkgs
  fetchNixpkgs = iohkNix.fetchNixpkgs ./nixpkgs-src.json;
  pkgs = import fetchNixpkgs { config = {}; overlays = []; };
  lib = pkgs.lib;
  cleanSourceHaskell = iohkNix.cleanSourceHaskell pkgs;
  getPackages = iohkNix.getPackages { inherit lib;};

  importPkgs = args: import fetchNixpkgs ({ overlays = [ iohkNix.jemallocOverlay ]; config = {}; } // args);

  # List of all plutus pkgs. This is used for `isPlutus` filter and `mapTestOn`
  plutusPkgList = [
    "core-to-plc"
    "language-plutus-core"
    "plutus-core-interpreter"
    "plutus-exe"
    "plutus-ir"
    "plutus-th"
    "plutus-use-cases"
    "wallet-api"
  ];


  isPlutus = name: builtins.elem name plutusPkgList;

in lib // {
  inherit fetchNixpkgs importPkgs cleanSourceHaskell getPackages iohkNix isPlutus plutusPkgList;
}
