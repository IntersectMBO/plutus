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
  # probably replace with failOnAllWarnings from the haskell lib once we're on a newer nixpkgs
  addWerror = drv: appendConfigureFlag drv "--ghc-option=-Werror";
  filterSource = drv: drv.overrideAttrs (attrs : {
    src = builtins.filterSource cleanSourceFilter attrs.src;
  });
  cleanSourceFilter = with pkgs.stdenv;
    name: type: let baseName = baseNameOf (toString name); in ! (
      # Filter out .git repo
      (type == "directory" && baseName == ".git") ||
      lib.hasSuffix "~" baseName ||
      builtins.match "^\\.sw[a-z]$" baseName != null ||
      builtins.match "^\\..*\\.sw[a-z]$" baseName != null ||
      builtins.match "^\\.ghc\\.environment\\..*$" baseName != null ||
      baseName == "dist" || baseName == "dist-newstyle" ||
      baseName == "cabal.project.local" ||
      lib.hasSuffix ".nix" baseName ||
      lib.hasSuffix ".dhall" baseName ||
      (type == "symlink" && lib.hasPrefix "result" baseName) ||
      (type == "directory" && baseName == ".stack-work")
    );
  plutusPkgs = (import ./pkgs { inherit pkgs; }).override {
    overrides = self: super: {
      # we want to enable benchmarking, which also means we have criterion in the corresponding env
      # we need to enable benchmarks as a flag too, until we are on a newer nixpkgs where this is implied by doBenchmark
      language-plutus-core = addWerror (appendConfigureFlag (doBenchmark (doHaddockHydra (addRealTimeTestLogs (filterSource super.language-plutus-core)))) "--enable-benchmarks");
      plutus-core-interpreter = addWerror (doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-core-interpreter)));
      plutus-exe = addWerror (addRealTimeTestLogs (filterSource super.plutus-exe));
      core-to-plc = addWerror (doHaddockHydra (addRealTimeTestLogs (filterSource super.core-to-plc)));
      plutus-ir = addWerror (doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-ir)));
      plutus-th = addWerror (doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-th)));
      plutus-use-cases = addWerror (addRealTimeTestLogs (filterSource super.plutus-use-cases));
      wallet-api = addWerror (doHaddockHydra (addRealTimeTestLogs (filterSource super.wallet-api)));
    };
  };
  other = rec {
    tests = let
      src = localLib.cleanSourceTree ./.;
    in {
      shellcheck = pkgs.callPackage ./tests/shellcheck.nix { inherit src; };
      hlint = pkgs.callPackage ./tests/hlint.nix { inherit src; };
      stylishHaskell = pkgs.callPackage ./tests/stylish.nix {
        inherit (plutusPkgs) stylish-haskell;
        inherit src;
      };
    };
    stack2nix = import (pkgs.fetchFromGitHub {
      owner = "avieth";
      repo = "stack2nix";
      rev = "c51db2d31892f7c4e7ff6acebe4504f788c56dca";
      sha256 = "10jcj33sxpq18gxf3zcck5i09b2y4jm6qjggqdlwd9ss86wg3ksb";
    }) { inherit pkgs; };
    plutus-core-spec = pkgs.callPackage ./plutus-core-spec {};
  };
in plutusPkgs // other
