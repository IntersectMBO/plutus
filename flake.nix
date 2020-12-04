{
  description = "Flake for Plutus";

  inputs = {
    nixpkgs.url =
      "github:NixOS/nixpkgs?rev=d105075a1fd870b1d1617a6008cb38b443e65433";
    # haskell-nix.url = "github:input-output-hk/haskell.nix";
    haskell-nix.url = "path:/home/manveru/github/input-output-hk/haskell.nix";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, haskell-nix, flake-utils, ... }:
    (flake-utils.lib.eachSystem [ "x86_64-linux" ] (system: rec {
      overlay = import ./overlay.nix { inherit system self; };

      legacyPackages = nixpkgs.legacyPackages.${system};

      packages = let
        inherit (import ./nix { }) ownOverlays;
        sources = let
          sourcesInfo =
            builtins.fromJSON (builtins.readFile ./nix/sources.json);
          fetch = sourceInfo:
            builtins.fetchTarball { inherit (sourceInfo) url sha256; };
        in builtins.mapAttrs (_: fetch) sourcesInfo;

        iohkNix = import sources.iohk-nix { };
        overlays = [
          haskell-nix.overlay
        ]
        # haskell-nix.haskellLib.extra: some useful extra utility functions for haskell.nix
          ++ iohkNix.overlays.haskell-nix-extra
          # iohkNix: nix utilities and niv:
          ++ iohkNix.overlays.iohkNix
          # our own overlays:
          ++ [
            # Modifications to derivations from nixpkgs
            (import ./nix/overlays/nixpkgs-overrides.nix)
            # This contains musl-specific stuff, but it's all guarded by appropriate host-platform
            # checks, so we can include it unconditionally
            (import ./nix/overlays/musl.nix)
            # fix r-modules
            (import ./nix/overlays/r.nix)
          ];
        pkgs = import nixpkgs {
          config = {
            allowUnfreePredicate = (import ./lib.nix).unfreePredicate;
          };
          localSystem = system;
          overlays = overlays;
        };

        plutusMusl = import sources.nixpkgs {
          inherit system;
          crossSystem = pkgs.lib.systems.examples.musl64;
          overlays = overlays;
          config = haskell-nix.config // {
            allowUnfreePredicate = (import ./lib.nix).unfreePredicate;
          };
        };

        rev = null;

        plutus = import ./nix/pkgs {
          inherit rev pkgs plutusMusl sources;
          checkMaterialization = false;
        };
      in plutus;

      apps.web-ghc = flake-utils.lib.mkApp { drv = legacyPackages.web-ghc; };
    }));
}
