{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
, sources ? import ./sources.nix { } // sourcesOverride
, haskellNix ? import sources."haskell.nix" {
    sourcesOverride = {
      hackage = sources."hackage.nix";
      stackage = sources."stackage.nix";
    };
  }
  # haskell-nix has to be used differently in flakes/no-flakes scenarios:
  # - When imported from flakes, 'haskellNix.overlay' needs to be passed here.
  # - When imported from default.nix without flakes, default to haskellNix.overlays
, haskellNixOverlays ? haskellNix.overlays
, checkMaterialization ? false
, enableHaskellProfiling ? false
}:
let
  ownOverlays =
    [
      # Modifications to derivations from nixpkgs
      (import ./overlays/nixpkgs-overrides.nix)
      # fix r-modules
      (import ./overlays/r.nix)
    ];

  extraOverlays = haskellNixOverlays ++ ownOverlays;

  pkgs = import sources.nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

  plutus = import ./pkgs { inherit pkgs checkMaterialization enableHaskellProfiling sources; };

in
{
  inherit pkgs plutus sources ownOverlays;
}
