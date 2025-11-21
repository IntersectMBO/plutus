# We maintain a fork of fourmolu that fixes some issues with the upstream version.

{ pkgs, lib }:

ghc:

let
  fourmolu-project = pkgs.haskell-nix.cabalProject' {
    src = pkgs.fetchFromGitHub {
      owner = "zeme-wana";
      repo = "fourmolu";
      rev = "3644b248a6ce19a85cce46edb20f5de08cb7546a";
      sha256 = "sha256-zyEkx4oKHQepPb+52dNVkg93SZHWeVf6JqM5WFOmqJE=";
    };
    compiler-nix-name = ghc;
  };
in

fourmolu-project.hsPkgs.fourmolu.components.exes.fourmolu
