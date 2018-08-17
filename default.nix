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
  doHaddockHydra = drv: overrideCabal drv (attrs: {
    doHaddock = true;
    postInstall = ''
      ${attrs.postInstall or ""}
      mkdir -pv $doc/nix-support
      tar -czvf $doc/${attrs.pname}-docs.tar.gz -C $doc/share/doc/html .
      echo "file binary-dist $doc/${attrs.pname}-docs.tar.gz" >> $doc/nix-support/hydra-build-products
      echo "report ${attrs.pname}-docs.html $doc/share/doc/html index.html" >> $doc/nix-support/hydra-build-products
    '';
  });
  addRealTimeTestLogs = drv: overrideCabal drv (attrs: {
    testTarget = "--show-details=streaming";
  });
  plutusPkgs = (import ./pkgs { inherit pkgs; }).override {
    overrides = self: super: {
      plutus-prototype = addRealTimeTestLogs super.plutus-prototype;
      language-plutus-core = doHaddockHydra (addRealTimeTestLogs super.language-plutus-core);
    };
  };
  cleanSourceFilter = with pkgs.stdenv;
    name: type: let baseName = baseNameOf (toString name); in ! (
      # Filter out .git repo
      (type == "directory" && baseName == ".git") ||
      # Filter out editor backup / swap files.
      lib.hasSuffix "~" baseName ||
      builtins.match "^\\.sw[a-z]$" baseName != null ||
      builtins.match "^\\..*\\.sw[a-z]$" baseName != null ||

      # Filter out locally generated/downloaded things.
      baseName == "dist" ||

      # Filter out the files which I'm editing often.
      lib.hasSuffix ".nix" baseName ||
      lib.hasSuffix ".dhall" baseName ||
      # Filter out nix-build result symlinks
      (type == "symlink" && lib.hasPrefix "result" baseName) ||
      (type == "directory" && baseName == ".stack-work")
    );
  source = builtins.filterSource cleanSourceFilter ./.;
  other = rec {
    tests = {
      shellcheck = pkgs.callPackage ./tests/shellcheck.nix { src = ./.; };
    };
    stack2nix = import (pkgs.fetchFromGitHub {
      owner = "avieth";
      repo = "stack2nix";
      rev = "c51db2d31892f7c4e7ff6acebe4504f788c56dca";
      sha256 = "10jcj33sxpq18gxf3zcck5i09b2y4jm6qjggqdlwd9ss86wg3ksb";
    }) { inherit pkgs; };
  };
in plutusPkgs // other
