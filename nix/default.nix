{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
, sources
, isInFlake
, haskellNix
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

  iohkNixMain = import sources.iohk-nix { };

  # haskell-nix has to be used differently in flakes/no-flakes scenarios:
  # - When imported from flakes, 'haskellNix.overlay' needs to be passed here.
  # - When imported from default.nix without flakes, default to haskellNix.overlays
  haskellNixOverlays = if isInFlake then [ haskellNix.overlay ] else haskellNix.overlays;

  # haskell-nix provides some global config settings but it's exposed under different
  # attribute paths when imported as flake/non-flake.
  haskellNixConfig = if isInFlake then haskellNix.internal.config else haskellNix.config;

  extraOverlays =
    # Haskell.nix (https://github.com/input-output-hk/haskell.nix)
    haskellNixOverlays
    # our own overlays:
    # needed for cardano-api wich uses a patched libsodium
    ++ iohkNixMain.overlays.crypto
    ++ ownOverlays;

  pkgs = import sources.nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNixConfig // config;
  };

  plutus = import ./pkgs { inherit pkgs checkMaterialization enableHaskellProfiling sources; };

in
{
  inherit pkgs plutus sources;
}
