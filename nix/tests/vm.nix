{ pkgs
, marlowe-playground
, marlowe-dashboard
, web-ghc
, plutus-pab
, marlowe-pab
, docs
, vmCompileTests
, sources
}:
let
  inherit (pkgs.stdenv) isDarwin;
  testing = import (pkgs.path + "/nixos/lib/testing-python.nix") { system = builtins.currentSystem; };
  makeTest = testing.makeTest;
  tests = pkgs.recurseIntoAttrs {
    marlowe-playground-server = pkgs.callPackage ./vm-tests/marlowe-playground.nix { inherit makeTest marlowe-playground; };
    web-ghc = pkgs.callPackage ./vm-tests/web-ghc.nix { inherit makeTest web-ghc sources; };
    pab = pkgs.callPackage ./vm-tests/pab.nix { inherit makeTest plutus-pab marlowe-pab marlowe-dashboard; };
    all = pkgs.callPackage ./vm-tests/all.nix { inherit makeTest marlowe-playground marlowe-dashboard web-ghc plutus-pab marlowe-pab docs vmCompileTests sources; };
  };
in
if isDarwin then { } else tests
