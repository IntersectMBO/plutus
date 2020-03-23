{ system ? builtins.currentSystem
, crossSystem ? null
, config ? {}
, overlays ? []
, sourcesOverride ? {}
}:
let
  sources = import ./sources.nix { inherit pkgs; }
    // sourcesOverride;
  iohkNix = import sources.iohk-nix {};
  haskellNix = import sources."haskell.nix";
  # Use our own nixpkgs
  nixpkgs = sources.nixpkgs;

  # for inclusion in pkgs:
  extraOverlays =
    # Haskell.nix (https://github.com/input-output-hk/haskell.nix)
    haskellNix.overlays
    # haskell-nix.haskellLib.extra: some useful extra utility functions for haskell.nix
    ++ iohkNix.overlays.haskell-nix-extra
    # iohkNix: nix utilities and niv:
    ++ iohkNix.overlays.iohkNix
    # our own overlays:
    ++ [
      (pkgs: _: with pkgs; {

        # commonLib: mix pkgs.lib with iohk-nix utils and our own:
        commonLib = lib // iohkNix
          // import ./util.nix { inherit lib haskell-nix; }
          # also expose our sources and overlays
          // { inherit overlays sources; };
      })
      (import ./overlays/nixpkgs-overrides.nix)
    ];

  pkgs = import nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

in pkgs
