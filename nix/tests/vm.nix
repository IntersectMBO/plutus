{ pkgs
, plutus-playground
, web-ghc
, docs
, vmCompileTests
}:
let
  inherit (pkgs.stdenv) isDarwin;
  testing = import (pkgs.path + "/nixos/lib/testing-python.nix") { system = builtins.currentSystem; };
  makeTest = testing.makeTest;
  tests = pkgs.recurseIntoAttrs {
    plutus-playground-server = pkgs.callPackage ./vm-tests/plutus-playground.nix { inherit makeTest plutus-playground; };
    web-ghc = pkgs.callPackage ./vm-tests/web-ghc.nix { inherit makeTest web-ghc; };
    all = pkgs.callPackage ./vm-tests/all.nix { inherit makeTest plutus-playground web-ghc docs vmCompileTests; };
  };
in
if isDarwin then { } else tests
