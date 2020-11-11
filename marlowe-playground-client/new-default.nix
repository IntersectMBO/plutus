{ pkgs, set-git-rev, haskell, docs, easyPS, webCommon, nodejs-headers }:

let
  buildPursProject = pkgs.callPackage ../nix/purescript.nix {
    inherit easyPS webCommon nodejs-headers;
    nodejs = pkgs.nodejs-10_x;
    nodePackages = pkgs.nodePackages_10_x;
  };

  buildPlayground = pkgs.callPackage ../nix/lib/build-playground.nix {
    inherit nodejs-headers easyPS webCommon;
    inherit buildPursProject;
  };

  runtimeGhc = haskell.packages.ghcWithPackages (ps: [ ps.marlowe ps.marlowe-playground-server ]);

  playground-exe = set-git-rev haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server;

  playground-exe-name = "marlowe-playground-server";

  client = buildPlayground {
    srcDir = ./.;
    name = "marlowe-playground-client";
    pscPackages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
    inherit runtimeGhc;
    inherit playground-exe playground-exe-name;
  };
in
{
  tutorial = docs.marlowe-tutorial;
  inherit client;
}
