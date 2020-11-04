{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, overlays ? [ ]
, sourcesOverride ? { }
, rev ? null
, checkMaterialization ? false
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

  extraOverlays =
    # Haskell.nix (https://github.com/input-output-hk/haskell.nix)
    haskellNix.overlays
    # haskell-nix.haskellLib.extra: some useful extra utility functions for haskell.nix
    ++ iohkNix.overlays.haskell-nix-extra
    # iohkNix: nix utilities and niv:
    ++ iohkNix.overlays.iohkNix
    # our own overlays:
    ++ [
      # Modifications to derivations from nixpkgs
      (import ./overlays/nixpkgs-overrides.nix)
      # This contains musl-specific stuff, but it's all guarded by appropriate host-platform
      # checks, so we can include it unconditionally
      (import ./overlays/musl.nix)
      # add pre-commit-hooks which isn't available in 20.03
      (import ./overlays/pre-commit-hooks.nix)
      # fix r-modules
      (import ./overlays/r.nix)
    ];

  pkgs = import sources.nixpkgs {
    inherit system crossSystem;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

  pkgsMusl = import sources.nixpkgs {
    system = "x86_64-linux";
    crossSystem = pkgs.lib.systems.examples.musl64;
    overlays = extraOverlays ++ overlays;
    config = haskellNix.config // config;
  };

  pkgsLocal = import ./pkgs { inherit rev pkgs pkgsMusl checkMaterialization sources; };

in
{
  inherit pkgs pkgsMusl pkgsLocal;
}
