let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, pkgs ? (import (localLib.fetchNixPkgs) { inherit system config; })
}:

let 
  plutusPkgs = import ./. {};
  ghc = pkgs.haskell.packages.ghc802.ghcWithPackages (ps: [plutusPkgs.plutus-prototype]);

in
  # This is an environment for running the frontend deps regeneration script.
  pkgs.stdenv.mkDerivation {
    name = "explorer-frontend-shell";
    buildInputs = with pkgs; [ ghc ];
    src = null;
  }
