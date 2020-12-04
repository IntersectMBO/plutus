{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
, sources ? import ./sources.nix { }
    // sourcesOverride
, haskellNix ? import sources."haskell.nix" {
    sourcesOverride = {
      hackage = sources."hackage.nix";
      stackage = sources."stackage.nix";
    };
  }
, haskellNixOverlays ? haskellNix.overlays
, rev ? null
, checkMaterialization ? false
}:
let
  iohkNix = import sources.iohk-nix { };

  ownOverlays =
    # haskell-nix.haskellLib.extra: some useful extra utility functions for haskell.nix
    iohkNix.overlays.haskell-nix-extra
    # iohkNix: nix utilities and niv:
    ++ iohkNix.overlays.iohkNix
    # our own overlays:
    ++ [
      # Modifications to derivations from nixpkgs
      (import ./overlays/nixpkgs-overrides.nix { inherit sources; })
      # This contains musl-specific stuff, but it's all guarded by appropriate host-platform
      # checks, so we can include it unconditionally
      (import ./overlays/musl.nix)
      # fix r-modules
      (import ./overlays/r.nix)
    ];

  extraOverlays =
    # Haskell.nix (https://github.com/input-output-hk/haskell.nix)
    haskellNixOverlays ++ ownOverlays;

  pkgs = import sources.nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

  plutusMusl = import sources.nixpkgs {
    system = "x86_64-linux";
    crossSystem = pkgs.lib.systems.examples.musl64;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

  plutus = import ./pkgs { inherit rev pkgs plutusMusl checkMaterialization sources; };

in
{
  inherit pkgs plutusMusl plutus ownOverlays;
}
