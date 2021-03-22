{ plutus ? import ./../.. { } }:
let
  pkgs = plutus.pkgs;
  testing = import (pkgs.path + "/nixos/lib/testing-python.nix") { system = builtins.currentSystem; };
  makeTest = testing.makeTest;
in
{
  plutus-playground-server = pkgs.callPackage ./vm-tests/plutus-playground.nix { inherit makeTest;inherit (plutus) plutus-playground; };
}
