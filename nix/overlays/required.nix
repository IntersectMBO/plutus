{ pkgs, enableProfiling }:

with import ../../lib.nix;

with pkgs.haskell.lib;

let
  addRealTimeTestLogs = drv: overrideCabal drv (attrs: {
    testTarget = "--show-details=streaming";
  });
in

self: super: {

    ########################################################################
    # Overides of Cardano SL packages

    ########################################################################
    language-plutus-core = addRealTimeTestLogs super.language-plutus-core;
    # The base Haskell package builder

    mkDerivation = args: super.mkDerivation (args // {
      enableLibraryProfiling = enableProfiling;
      enableExecutableProfiling = enableProfiling;
      splitCheck = true;
      # Static linking for everything to work around
      # https://ghc.haskell.org/trac/ghc/ticket/14444
      # This will be the default in nixpkgs since
      # https://github.com/NixOS/nixpkgs/issues/29011
      enableSharedExecutables = false;
    } // pkgs.lib.optionalAttrs (args ? src) {
      src = cleanSourceHaskell args.src;
    });
  }
