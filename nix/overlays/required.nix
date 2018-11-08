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
    # Overides of local packages

    ########################################################################
    language-plutus-core = addRealTimeTestLogs super.language-plutus-core;
    # The base Haskell package builder

    mkDerivation = args: super.mkDerivation (args // {
      enableLibraryProfiling = enableProfiling;
      enableExecutableProfiling = enableProfiling;
      splitCheck = true;
    } // pkgs.lib.optionalAttrs (args ? src) {
      src = cleanSourceHaskell args.src;
    });
  }
