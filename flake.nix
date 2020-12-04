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

      packages = let inherit (import ./nix { }) ownOverlays;
      in import ./nix {
        inherit system;
        config = { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; };
        rev = self.rev;
        pkgs = { overlays, config, ... }:
          import nixpkgs {
            inherit config;
            overlays = [ haskell-nix.overlay ] ++ ownOverlays;
          };
      };

      apps.web-ghc = flake-utils.lib.mkApp { drv = legacyPackages.web-ghc; };
    }));
}
