{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
}:
let
  sources = import ./sources.nix { inherit pkgs; }
    // sourcesOverride;
  iohkNix = import sources.iohk-nix { };
  haskellNix = import sources."haskell.nix" {
    sourcesOverride = {
      hackage = sources."hackage.nix";
      stackage = sources."stackage.nix";
    };
  };
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
      # This contains musl-specific stuff, but it's all guarded by appropriate host-platform
      # checks, so we can include it unconditionally
      (import ./overlays/musl.nix)
      # add pre-commit-hooks which isn't available in 20.03
      (import ./overlays/pre-commit-hooks.nix)
      # fix r-modules
      (import ./overlays/r.nix)
    ];

  pkgs = import nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

in
pkgs
