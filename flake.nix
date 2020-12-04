{
  description = "Flake for Plutus";

  inputs = {
    nixpkgs.url =
      "github:NixOS/nixpkgs?rev=d105075a1fd870b1d1617a6008cb38b443e65433";
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    # haskell-nix.url = "path:/home/manveru/github/input-output-hk/haskell.nix";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, haskell-nix, flake-utils, ... }:
    (flake-utils.lib.eachSystem [ "x86_64-linux" "x86_64-darwin" ] (system:
      let
        sources =
          let
            sourcesInfo =
              builtins.fromJSON (builtins.readFile ./nix/sources.json);
            fetch = sourceInfo:
              builtins.fetchTarball { inherit (sourceInfo) url sha256; };
          in
          builtins.mapAttrs (_: fetch) sourcesInfo
          // { inherit nixpkgs; };
        plutusPackages = import ./nix {
          inherit system sources;
          rev = "TODO-fix-flake-rev";
          haskellNixOverlays = [ haskell-nix.overlay ];
        };
        inherit (plutusPackages) pkgs plutusMusl plutus ownOverlays;
      in
      rec {
        legacyPackages = pkgs;
        # overlays = ownOverlays;

        packages = {
          web-ghc-server = plutus.haskell.project.hsPkgs.web-ghc.components.exes.web-ghc-server;
        };

        devShell = import ./shell.nix { packages = plutusPackages; };

        apps.web-ghc = flake-utils.lib.mkApp {
          exePath = "/bin/web-ghc-server"; # This is only needed because haskell.nix exePath includes $out
          drv = packages.web-ghc-server;
        };
      }));
}
