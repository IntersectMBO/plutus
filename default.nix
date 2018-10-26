{ system ? builtins.currentSystem
, nixpkgs ? import ./overrideableFetchNixPkgs.nix
, config ? {}
}:

let
  jemallocOverlay = self: super: {
    # jemalloc has a bug that caused cardano-sl-db to fail to link (via
    # rocksdb, which can use jemalloc).
    # https://github.com/jemalloc/jemalloc/issues/937
    # Using jemalloc 510 with the --disable-initial-exec-tls flag seems to
    # fix it.
    jemalloc = self.callPackage ./nix/jemalloc/jemalloc510.nix {};
  };
  pkgs = import nixpkgs { inherit system config; overlays = [ jemallocOverlay ]; };
in
let
  doHaddockHydra = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    doHaddock = true;
    postInstall = ''
      ${attrs.postInstall or ""}
      mkdir -pv $doc/nix-support
      tar -czvf $doc/${attrs.pname}-docs.tar.gz -C $doc/share/doc .
      echo "file binary-dist $doc/${attrs.pname}-docs.tar.gz" >> $doc/nix-support/hydra-build-products
      echo "report ${attrs.pname}-docs.html $doc/share/doc index.html" >> $doc/nix-support/hydra-build-products
    '';
  });
  addPatches = drv: patches: pkgs.haskell.lib.overrideCabal drv (attrs: {
    inherit patches;
  });
  addRealTimeTestLogs = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    testTarget = "--show-details=streaming";
  });
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
  plutusPkgs2 = (import ./pkgs {
    inherit pkgs;
    compiler = pkgs.haskell.packages.ghc843;
  }).override {
    overrides = self: super: ({
      plutus-prototype = addRealTimeTestLogs (filterSource super.plutus-prototype);
      # we want to enable benchmarking, which also means we have criterion in the corresponding env
      language-plutus-core = pkgs.haskell.lib.appendConfigureFlag (pkgs.haskell.lib.doBenchmark (doHaddockHydra (addRealTimeTestLogs (filterSource super.language-plutus-core)))) "--enable-benchmarks";
      plutus-core-interpreter = doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-core-interpreter));
      plutus-exe = addRealTimeTestLogs (filterSource super.plutus-exe);
      core-to-plc = doHaddockHydra (addRealTimeTestLogs (filterSource super.core-to-plc));
      plutus-th = doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-th));
      plutus-use-cases = addRealTimeTestLogs (filterSource super.plutus-use-cases);
      wallet-api = doHaddockHydra (addRealTimeTestLogs (filterSource super.wallet-api));
      mtl = null;
      text = null;
      stm_2_4_5_1 = self.callPackage
        ({
          mkDerivation
        , array
        , base
        , stdenv
        }:
        self.mkDerivation {
          pname = "stm";
          version = "2.4.5.1";
          sha256 = "6cf0c280062736c9980ba1c2316587648b8e9d4e4ecc5aed16a41979c0a3a3f4";
          libraryHaskellDepends = [ array base ];
          doHaddock = false;
          doCheck = false;
          homepage = "https://wiki.haskell.org/Software_transactional_memory";
          description = "Software Transactional Memory";
          license = stdenv.lib.licenses.bsd3;
        }) {};
    });
  };

  plutusPkgs = (import ./pkgs {
    inherit pkgs;
    compiler = pkgs.haskell.packages.ghcjs84;
  }).override {
    overrides = self: super: ({
      plutus-prototype = addRealTimeTestLogs (filterSource super.plutus-prototype);
      # we want to enable benchmarking, which also means we have criterion in the corresponding env
      language-plutus-core = pkgs.haskell.lib.appendConfigureFlag (pkgs.haskell.lib.doBenchmark (doHaddockHydra (addRealTimeTestLogs (filterSource super.language-plutus-core)))) "--enable-benchmarks";
      plutus-core-interpreter = doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-core-interpreter));
      plutus-exe = addRealTimeTestLogs (filterSource super.plutus-exe);
      plutus-th = doHaddockHydra (addRealTimeTestLogs (filterSource super.plutus-th));
      plutus-use-cases = addRealTimeTestLogs (filterSource super.plutus-use-cases);
      wallet-api = doHaddockHydra (addRealTimeTestLogs (filterSource super.wallet-api));
      mtl = null;
      text = null;
    } // ({
      cborg = addPatches super.cborg [ pkgs/cborg.patch ];
      stm_2_4_5_1 = self.callPackage
        ({
          mkDerivation
        , array
        , base
        , stdenv
        }:
        self.mkDerivation {
          pname = "stm";
          version = "2.4.5.1";
          sha256 = "6cf0c280062736c9980ba1c2316587648b8e9d4e4ecc5aed16a41979c0a3a3f4";
          libraryHaskellDepends = [ array base ];
          doHaddock = false;
          doCheck = false;
          homepage = "https://wiki.haskell.org/Software_transactional_memory";
          description = "Software Transactional Memory";
          license = stdenv.lib.licenses.bsd3;
        }) {};
    }));
  };
  other = rec {
    tests = let
      src = (import ./lib.nix { inherit pkgs; }).cleanSourceTree ./.;
    in {
      shellcheck = pkgs.callPackage ./tests/shellcheck.nix { inherit src; };
      hlint = pkgs.callPackage ./tests/hlint.nix { inherit src; };
      stylishHaskell = pkgs.callPackage ./tests/stylish.nix {
        inherit (plutusPkgs2) stylish-haskell;
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
