########################################################################
# default.nix -- The top-level nix build file for Plutus.
#
# This file defines various attributes that are used for building and
# developing Plutus.
#
########################################################################
{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { }
, sourcesOverride ? { }
, sources ? import ./nix/sources.nix { inherit system; } // sourcesOverride
, haskellNix ? import sources.haskell-nix {
    pkgs = import sources.nixpkgs { inherit system; };
    sourcesOverride = {
      hackage = sources.hackage-nix;
    };
  }
, packages ? import ./nix {
    inherit system sources crossSystem config sourcesOverride haskellNix;
  }
}:
let
  inherit (packages) pkgs plutus;
  inherit (plutus) haskell;
in
rec {
  inherit pkgs plutus;

  tests = import ./nix/tests/default.nix {
    inherit pkgs docs;
    inherit (plutus.lib) gitignore-nix;
    inherit (plutus) fixStylishHaskell fixPngOptimization fixCabalFmt;
    src = ./.;
  };

  docs = import ./nix/docs.nix { inherit pkgs plutus; };
}
