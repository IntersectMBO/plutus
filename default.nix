let
  localLib = import ./lib.nix;
  jemallocOverlay = self: super: {
    # jemalloc has a bug that caused cardano-sl-db to fail to link (via
    # rocksdb, which can use jemalloc).
    # https://github.com/jemalloc/jemalloc/issues/937
    # Using jemalloc 510 with the --disable-initial-exec-tls flag seems to
    # fix it.
    jemalloc = self.callPackage ./nix/jemalloc/jemalloc510.nix {};
  };
in
{ system ? builtins.currentSystem
, pkgs ? (import (localLib.fetchNixPkgs) { inherit system config; overlays = [ jemallocOverlay ]; })
, config ? {}
}:

with pkgs.lib;
with pkgs.haskell.lib;

let
  plutusPkgs = ((import ./pkgs { inherit pkgs; }).override {
    ghc = overrideDerivation pkgs.haskell.compiler.ghc802 (drv: {
      patches = drv.patches ++ [ ./ghc-8.0.2-darwin-rec-link.patch ];
    });
  });
  other = rec {
    stack2nix = import (pkgs.fetchFromGitHub {
      owner = "avieth";
      repo = "stack2nix";
      rev = "c51db2d31892f7c4e7ff6acebe4504f788c56dca";
      sha256 = "10jcj33sxpq18gxf3zcck5i09b2y4jm6qjggqdlwd9ss86wg3ksb";
    }) { inherit pkgs; };
  };
in plutusPkgs // other
