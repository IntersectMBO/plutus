{ pkgs }:

with import ../../lib.nix { inherit (pkgs) system config; };
with pkgs.haskell.lib;

let
  addRealTimeTestLogs = drv: overrideCabal drv (attrs: {
    testTarget = "--show-details=streaming";
  });
  doctest = opts: drv: overrideCabal drv (attrs: {
    postCheck = "./Setup doctest --doctest-options=\"${opts}\"";
  });
in

self: super: {

    ########################################################################
    # Overides of local packages
    language-plutus-core = addRealTimeTestLogs super.language-plutus-core;
    # cabal doctest doesn't seem to be clever enough to pick these up from the cabal file
    plutus-tx = doctest "-pgmL markdown-unlit -XTemplateHaskell -XDeriveFunctor -XScopedTypeVariables" super.plutus-tx;

    ########################################################################
    # The base Haskell package builder

    mkDerivation = args: super.mkDerivation (args //
      pkgs.lib.optionalAttrs (args ? src) {
        src = iohkNix.cleanSourceHaskell args.src;
    });

    # stack2nix doesn't have the right set of GHC base packages nulled out for 8.4, as
    # per https://github.com/input-output-hk/stack2nix/issues/84, which means
    # we can hit https://github.com/input-output-hk/stack2nix/issues/134 unless
    # we do it oursevles.
    mtl = null;
    parsec = null;
    stm = null;
    text = null;
    xhtml = null;
  }
