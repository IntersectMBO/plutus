# We maintain a fork of fourmolu that fixes some issues with the upstream version.

{ pkgs, lib }:

ghc:

let

  attrs = {
    "ghc96".rev = "0.17.0.0";
    "ghc96".sha256 = "";

    "ghc912".rev = "0.19.0.1";
    "ghc912".sha256 = "";
  }.${ghc};

  fourmolu-project = pkgs.haskell-nix.cabalProject' {
    src = pkgs.fetchFromGitHub {
      owner = "zeme-wana";
      repo = "fourmolu";
      inherit (attrs) rev sha256;
    };
    compiler-nix-name = ghc;
  };

in

fourmolu-project.hsPkgs.fourmolu.components.exes.fourmolu
