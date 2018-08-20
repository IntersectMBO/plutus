# TODO: replace with shellFor once our pinned nixpkgs advances past 
# 5523ec8f3c78704c6e76b7675bfce41d24a3feb1, before which it doesn't
# handle overridden dependencies properly
let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, pkgs ? (import (localLib.fetchNixPkgs) { inherit system config; })
}:

let 
  plutusPkgs = import ./. {};
  ghc = pkgs.haskell.packages.ghc822.ghcWithPackages (ps: [
    plutusPkgs.plutus-prototype 
    plutusPkgs.language-plutus-core 
    plutusPkgs.tasty-hedgehog
    plutusPkgs.tasty
    plutusPkgs.tasty-golden
    plutusPkgs.tasty-hunit
    plutusPkgs.hedgehog
  ]);

in
  # This is an environment for running the deps regeneration script.
  pkgs.stdenv.mkDerivation {
    name = "plutus-ghc";
    buildInputs = with pkgs; [ ghc ];
    src = null;
  }
