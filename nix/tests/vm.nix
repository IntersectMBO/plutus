{ plutus ? import ./../.. { } }:
let
  pkgs = plutus.pkgs;
  testing = import (pkgs.path + "/nixos/lib/testing-python.nix") { system = builtins.currentSystem; };
  makeTest = testing.makeTest;
in
{
  plutus-playground-server = pkgs.callPackage ./vm-tests/plutus-playground.nix { inherit makeTest;inherit (plutus) plutus-playground; };
  marlowe-playground-server = pkgs.callPackage ./vm-tests/marlowe-playground.nix { inherit makeTest;inherit (plutus) marlowe-playground; };
  web-ghc = pkgs.callPackage ./vm-tests/web-ghc.nix { inherit makeTest;inherit (plutus) web-ghc; };
  pab = pkgs.callPackage ./vm-tests/pab.nix { inherit makeTest;inherit (plutus) plutus-pab marlowe-dashboard; };
}
