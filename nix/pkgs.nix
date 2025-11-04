{ inputs, system }:

# Provides `pkgs` with project overlays and workarounds.
import inputs.nixpkgs {
  inherit system;
  config = inputs.haskell-nix.config;
  overlays = [
    inputs.iohk-nix.overlays.crypto
    inputs.iohk-nix.overlays.cardano-lib
    inputs.haskell-nix.overlay
    inputs.iohk-nix.overlays.haskell-nix-crypto
    inputs.iohk-nix.overlays.haskell-nix-extra

    # Disable the libsigsegv test suite on x86_64-darwin.
    #
    # On Apple Silicon machines using older Rosetta releases,
    # libsigsegv's stack overflow tests fail with "Abort trap"
    # due to incomplete emulation of synchronous exceptions.
    #
    # Newer Rosetta versions (e.g. darwin24.6.0) do not exhibit this issue,
    # so this workaround can be removed once those versions are widespread.
    #
    # This package is a transitive dependency of TeX Live,
    # so without this overlay TeX Live cannot be built with affected
    # Rosetta versions.
    #
    # TODO: Remove this once `ci.iog.io` macOS builders are updated to a
    # newer version of macOS.
    (final: prev: {
      libsigsegv = prev.libsigsegv.overrideAttrs (old: {
        doCheck = old.doCheck && prev.stdenv.hostPlatform.system != "x86_64-darwin";
      });
    })
  ];
}
