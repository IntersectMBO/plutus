{ pkgs
, plutus-playground
, marlowe-playground
, marlowe-dashboard
, web-ghc
, plutus-pab
, marlowe-app
, marlowe-companion-app
, vmCompileTests
}:
let
  inherit (pkgs.stdenv) isDarwin;
  testing = import (pkgs.path + "/nixos/lib/testing-python.nix") { system = builtins.currentSystem; };
  makeTest = testing.makeTest;
  tests = pkgs.recurseIntoAttrs {
    plutus-playground-server = pkgs.callPackage ./vm-tests/plutus-playground.nix { inherit makeTest plutus-playground; };
    marlowe-playground-server = pkgs.callPackage ./vm-tests/marlowe-playground.nix { inherit makeTest marlowe-playground; };
    web-ghc = pkgs.callPackage ./vm-tests/web-ghc.nix { inherit makeTest web-ghc; };
    pab = pkgs.callPackage ./vm-tests/pab.nix { inherit makeTest plutus-pab marlowe-dashboard; };
    all = pkgs.callPackage ./vm-tests/all.nix { inherit makeTest plutus-playground marlowe-playground marlowe-dashboard web-ghc marlowe-app marlowe-companion-app plutus-pab vmCompileTests; };
  };
in
if isDarwin then { } else tests
