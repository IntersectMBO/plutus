let
  # Allow overriding pinned nixpkgs for debugging purposes via plutus_pkgs
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
  fetchNixpkgs = iohkNix.fetchNixpkgs ./nixpkgs-src.json;
  pkgs = import fetchNixpkgs { config = {}; overlays = []; };
  lib = pkgs.lib;
  cleanSourceHaskell = iohkNix.cleanSourceHaskell pkgs;
  getPackages = iohkNix.getPackages { inherit lib;};

  importPkgs = args: import fetchNixpkgs ({ overlays = [ iohkNix.jemallocOverlay ]; } // args);


  isPlutus = name: (lib.hasPrefix "plutus" name) || (lib.hasPrefix "language-plutus" name);

in lib // {
  inherit fetchNixpkgs importPkgs cleanSourceHaskell iohkNix isPlutus getPackages;
  inherit (iohkNix) maybeEnv;
}
