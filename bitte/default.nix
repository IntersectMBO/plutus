{ marlowe-playground, plutus-playground, web-ghc, marlowe-pab, marlowe-dashboard, marlowe-web, docs, pkgs }:
let
  staticSite = pkgs.callPackage ./static-site.nix { };
  playgroundStatic = pkgs.callPackage ./playground-static.nix { inherit staticSite; docs = docs.site; };
in
{
  web-ghc-server-entrypoint = pkgs.callPackage ./web-ghc-server.nix {
    web-ghc-server = web-ghc;
  };

  plutus-playground-server-entrypoint = pkgs.callPackage ./plutus-playground-server.nix {
    variant = "plutus";
    pkg = plutus-playground.server;
    port = 4003;
  };
  plutus-playground-client-entrypoint = playgroundStatic {
    client = plutus-playground.client;
    variant = "plutus";
    port = 8081;
  };

  marlowe-playground-server-entrypoint = pkgs.callPackage ./plutus-playground-server.nix {
    variant = "marlowe";
    pkg = marlowe-playground.server;
    port = 4004;
  };
  marlowe-playground-client-entrypoint = playgroundStatic {
    client = marlowe-playground.client;
    variant = "marlowe";
    port = 8087;
  };

  marlowe-run-entrypoint = pkgs.callPackage ./pab.nix {
    pabExe = "${marlowe-pab}/bin/marlowe-pab";
    staticPkg = marlowe-dashboard.client;
  };

  marlowe-website-entrypoint = staticSite {
    root = marlowe-web;
    port = 8088;
  };
}
