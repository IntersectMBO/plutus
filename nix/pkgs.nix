{ inputs, system }:

import inputs.nixpkgs {
  inherit system;
  config = inputs.haskell-nix.config;
  overlays = [
    inputs.iohk-nix.overlays.crypto
    inputs.iohk-nix.overlays.cardano-lib
    inputs.haskell-nix.overlay
    inputs.iohk-nix.overlays.haskell-nix-crypto
    inputs.iohk-nix.overlays.haskell-nix-extra
    # Pin R to 4.4.3 until inline-r is fixed.
    # See https://github.com/tweag/HaskellR/issues/431
    (final: prev: {
      R = prev.R.overrideAttrs rec {
        version = "4.4.3";
        src = final.fetchurl {
          url = "https://cran.r-project.org/src/base/R-${
            final.lib.versions.major version}/R-${version}.tar.gz";
          hash = "sha256-DZPSJEQt6iU8KwhvCI220NPP2bWSzVSW6MshQ+kPyeg=";
        };
      };
    })
  ];
}
