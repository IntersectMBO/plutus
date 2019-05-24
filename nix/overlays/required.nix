{ pkgs }:

with import ../../lib.nix { inherit (pkgs) system config; };
with pkgs.haskell.lib;

let
  addRealTimeTestLogs = drv: overrideCabal drv (attrs: {
    testTarget = "--show-details=streaming";
  });
  # We do this for things where we need to run the plugin, but where Haddock chokes on it. We can't just turn it off,
  # so we run it with deferred errors. This runs the slight risk that we will miss a real error until runtime, but
  # we only do this in the CI build, so we should be okay.
  deferPluginErrors = drv: appendConfigureFlag drv "-f defer-plugin-errors";
  doctest = opts: drv: overrideCabal drv (attrs: {
    postCheck = "./Setup doctest --doctest-options=\"${opts}\"";
  });
  # cabal doctest doesn't seem to be clever enough to pick these up from the cabal file
  doctestOpts = "-pgmL markdown-unlit -XTemplateHaskell -XDeriveFunctor -XScopedTypeVariables -fno-ignore-interface-pragmas -fobject-code";
in

self: super: {

    ########################################################################
    # Overides of local packages
    language-plutus-core = addRealTimeTestLogs super.language-plutus-core;
    plutus-tx = doctest doctestOpts super.plutus-tx;
    plutus-tutorial = doctest doctestOpts (deferPluginErrors super.plutus-tutorial);
    plutus-use-cases = deferPluginErrors super.plutus-use-cases;
    plutus-playground-server = deferPluginErrors super.plutus-playground-server;
    plutus-wallet-api = deferPluginErrors super.plutus-wallet-api;
    marlowe = deferPluginErrors super.marlowe;

    ########################################################################
    # The base Haskell package builder

    mkDerivation = args: super.mkDerivation (args //
      pkgs.lib.optionalAttrs (args ? src) {
        src = iohkNix.cleanSourceHaskell args.src;
    });

    # Cuts down time for doctests by an order of magnitude, see https://gitlab.haskell.org/ghc/ghc/issues/15524
    # Should also not be necessary once we bump nixpkgs to 19.03 and --enable-library-for-ghci isn't the default
    doctest = enableSharedExecutables super.doctest;

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
