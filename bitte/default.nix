{ plutus-playground, web-ghc, docs, pkgs }:
let
  staticSite = pkgs.callPackage ./static-site.nix { };
  playgroundStatic = pkgs.callPackage ./playground-static.nix { inherit staticSite; docs = docs.site; };
in
{
  plutus-playground-server-entrypoint = pkgs.callPackage ./plutus-playground-server.nix {
    variant = "plutus";
    pkg = plutus-playground.server;
  };
  plutus-playground-client-entrypoint = playgroundStatic {
    client = plutus-playground.client;
    variant = "plutus";
  };
}
