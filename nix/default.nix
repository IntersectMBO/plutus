{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
, sources
, haskellNix
, checkMaterialization ? false
, enableHaskellProfiling ? false
}:
let
  ownOverlays =
    [
      # Modifications to derivations from nixpkgs
      (import ./overlays/nixpkgs-overrides.nix)
      # stdenv.lib is still needed by the pinned version of easy purescipt
      (final: prev: { stdenv = prev.stdenv // { inherit (final) lib; }; })
    ];

  iohkNixMain = import sources.iohk-nix { };

  extraOverlays =
    # Haskell.nix (https://github.com/input-output-hk/haskell.nix)
    haskellNix.nixpkgsArgs.overlays
    # our own overlays:
    # needed for cardano-api wich uses a patched libsodium
    ++ iohkNixMain.overlays.crypto
    ++ ownOverlays;

  pkgs = import sources.nixpkgs {
    inherit crossSystem;
    # In nixpkgs versions older than 21.05, if we don't explicitly pass
    # in localSystem we will hit a code path that uses builtins.currentSystem,
    # which breaks flake's pure evaluation.
    localSystem = { inherit system; };
    overlays = extraOverlays ++ overlays;
    config = haskellNix.nixpkgsArgs.config // config;
  };

  plutus-apps = import ./pkgs { inherit pkgs checkMaterialization enableHaskellProfiling sources; };

in
{
  inherit pkgs plutus-apps sources;
}
