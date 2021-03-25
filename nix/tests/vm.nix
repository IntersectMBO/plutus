{ pkgs
, plutus-playground
, marlowe-playground
, marlowe-dashboard
, web-ghc
, plutus-pab
, marlowe-app
}:
let
  testing = import (pkgs.path + "/nixos/lib/testing-python.nix") { system = builtins.currentSystem; };
  makeTest = testing.makeTest;
in
pkgs.recurseIntoAttrs {
  plutus-playground-server = pkgs.callPackage ./vm-tests/plutus-playground.nix { inherit makeTest;inherit plutus-playground; };
  marlowe-playground-server = pkgs.callPackage ./vm-tests/marlowe-playground.nix { inherit makeTest;inherit marlowe-playground; };
  web-ghc = pkgs.callPackage ./vm-tests/web-ghc.nix { inherit makeTest;inherit web-ghc; };
  pab = pkgs.callPackage ./vm-tests/pab.nix { inherit makeTest;inherit plutus-pab marlowe-dashboard; };
  all = pkgs.callPackage ./vm-tests/all.nix { inherit makeTest;inherit plutus-playground marlowe-playground marlowe-dashboard web-ghc marlowe-app plutus-pab; };
}
