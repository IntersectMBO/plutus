# We maintain a fork of fourmolu that fixes some issues with the upstream version.

{ pkgs, lib }:

ghc:

let

  attrs = {
    "ghc96".rev = "0.17.0.0";
    "ghc96".sha256 = "sha256-SzPmmpLOkRF6eLSSFzw/ZV1ERPvQOuIPfhZ/gpNpfZQ=";

    "ghc912".rev = "0.19.0.1";
    "ghc912".sha256 = "sha256-8A+LkCoXJj0edVe6lYEk5o0Nra+MC2Qm6i5Bribp1g4=";
  }.${ghc};

  fourmolu-project = pkgs.haskell-nix.cabalProject' {
    src = pkgs.fetchFromGitHub {
      owner = "zeme-wana";
      repo = "fourmolu";
      inherit (attrs) rev sha256;
    };
    compiler-nix-name = ghc;
    # The fork pins an old index-state whose ghc-lib-parser snapshot no longer
    # compiles with GHC 9.12.4; solve against a newer index instead.
    cabalProjectLocal = ''
      index-state: 2026-06-22T23:30:49Z
    '';
  };

in

fourmolu-project.hsPkgs.fourmolu.components.exes.fourmolu
