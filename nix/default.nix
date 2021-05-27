{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
, checkMaterialization ? false
, enableHaskellProfiling ? false
}:
let
  sources = import ./sources.nix { inherit pkgs; }
    // sourcesOverride;
  haskellNix = import sources."haskell.nix" {
    sourcesOverride = {
      hackage = sources."hackage.nix";
      stackage = sources."stackage.nix";
    };
  };

  extraOverlays =
    # Haskell.nix (https://github.com/input-output-hk/haskell.nix)
    haskellNix.overlays
    # our own overlays:
    ++ [
      # Modifications to derivations from nixpkgs
      (import ./overlays/nixpkgs-overrides.nix)
    ];

  pkgs = import sources.nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

  plutus = import ./pkgs { inherit pkgs checkMaterialization enableHaskellProfiling sources; };

in
{
  inherit pkgs plutus sources;
}
