########################################################################
# default.nix -- The top-level nix build file for plutus.
#
# This file defines an attribute set of packages.
#
# It contains:
#
#   - pkgs -- the nixpkgs set that the build is based on.
#   - haskellPackages.* -- the package set based on stackage
#   - haskellPackages.ghc -- the compiler
#   - localPackages -- just local packages
#
#   - tests -- integration tests and linters suitable for running in a
#              sandboxed build environment
#
# Other files:
#   - shell.nix   - dev environment, used by nix-shell / nix run.
#   - release.nix - the Hydra jobset.
#   - lib.nix     - the localLib common functions.
#   - nix/*       - other nix code modules used by this file.
#
# See also:
#   - TODO: documentation links
#
########################################################################

{ system ? builtins.currentSystem
, config ? {}  # The nixpkgs configuration file

# Use a pinned version nixpkgs.
, pkgs ? (import ./lib.nix { inherit config system; }).pkgs

# Disable running of tests for all local packages.
, forceDontCheck ? false

# Enable profiling for all haskell packages.
# Profiling slows down performance by 50% so we don't enable it by default.
, enableProfiling ? false

# Enable separation of build/check derivations.
, enableSplitCheck ? true

# Keeps the debug information for all haskell packages.
, enableDebugging ? false

# Build (but don't run) benchmarks for all local packages.
, enableBenchmarks ? true

# Overrides all nix derivations to add build timing information in
# their build output.
, enablePhaseMetrics ? true

# Overrides all nix derivations to add haddock hydra output.
, enableHaddockHydra ? true

# Disables optimization in the build for all local packages.
, fasterBuild ? false

# Forces all warnings as errors
, forceError ? true

}:

with pkgs.lib;

let
  localLib = import ./lib.nix { inherit config system; } ;
  src = localLib.iohkNix.cleanSourceHaskell ./.;
  errorOverlay = import ./nix/overlays/force-error.nix {
    inherit pkgs;
    filter = localLib.isPlutus;
  };
  customOverlays = optional forceError errorOverlay;
  purescriptNixpkgs = import (localLib.iohkNix.fetchNixpkgs ./plutus-playground/plutus-playground-client/nixpkgs-src.json) {};
  packages = self: (rec {
    inherit pkgs localLib;

    # This is the stackage LTS plus overrides, plus the plutus
    # packages.
    haskellPackages = self.callPackage localLib.iohkNix.haskellPackages {
      inherit forceDontCheck enableProfiling enablePhaseMetrics
      enableHaddockHydra enableBenchmarks fasterBuild enableDebugging
      enableSplitCheck customOverlays;
      pkgsGenerated = ./pkgs;
      filter = localLib.isPlutus;
      filterOverrides = {
        splitCheck = let
          dontSplit = [ 
            # Broken for things with test tool dependencies
            "wallet-api"
            "plutus-tx"
            # Broken for things which pick up other files at test runtime
            "plutus-playground-server"
          ];
          # Split only local packages not in the don't split list
          doSplit = builtins.filter (name: !(builtins.elem name dontSplit)) localLib.plutusPkgList;
          in name: builtins.elem name doSplit;
      };
      requiredOverlay = ./nix/overlays/required.nix;
    };

    # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
    playgroundGhc = haskellPackages.ghcWithPackages (ps: [
      haskellPackages.plutus-playground-server
      haskellPackages.plutus-playground-lib
      haskellPackages.plutus-use-cases
    ]);

    localPackages = localLib.getPackages {
      inherit (self) haskellPackages; filter = localLib.isPlutus;
    };
    tests = {
      shellcheck = pkgs.callPackage localLib.iohkNix.tests.shellcheck { inherit src; };
      hlint = pkgs.callPackage localLib.iohkNix.tests.hlint {
        inherit src;
        projects = let
                     fixPlaygroundServer = v: if v != "plutus-playground-server" then v else "plutus-playground/plutus-playground-server";
                     fixPlaygroundLib = v: if v != "plutus-playground-lib" then v else "plutus-playground/plutus-playground-lib";
                   in
                     map (localLib.comp fixPlaygroundServer fixPlaygroundLib) localLib.plutusHaskellPkgList;
      };
      stylishHaskell = pkgs.callPackage localLib.iohkNix.tests.stylishHaskell {
        inherit (self.haskellPackages) stylish-haskell;
        inherit src;
      };
    };
    plutus-server-invoker = pkgs.stdenv.mkDerivation {
      name = "plutus-server-invoker";
      unpackPhase = "true";
      buildInputs = [ playgroundGhc haskellPackages.plutus-playground-server pkgs.makeWrapper ];
      buildPhase = ''
        # We need to provide the ghc interpreter (hint) with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${haskellPackages.plutus-playground-server}/bin/plutus-playground-server $out/bin/plutus-playground-server
        wrapProgram $out/bin/plutus-playground-server --set GHC_LIB_DIR "${playgroundGhc}/lib/ghc-8.4.3" --set GHC_PACKAGE_PATH "${playgroundGhc}/lib/ghc-8.4.3/package.conf.d"
      '';
      installPhase = "echo nothing to install";
    };
    plutus-playground-purescript = pkgs.stdenv.mkDerivation {
        name = "plutus-playground-purescript";
        unpackPhase = "true";
        buildInputs = [ haskellPackages.plutus-playground-server ];
        buildPhase = ''
        mkdir $out
        ${haskellPackages.plutus-playground-server}/bin/plutus-playground-server psgenerator $out
        '';
        installPhase = "echo nothing to install";
    };
    inherit (pkgs.callPackage ./plutus-playground/plutus-playground-client {
         pkgs = purescriptNixpkgs;
         psSrc = plutus-playground-purescript;
    }) plutus-playground-client;
    docs = {
      plutus-core-spec = pkgs.callPackage ./plutus-core-spec {};
      lazy-machine = pkgs.callPackage ./docs/fomega/lazy-machine {};
    };
    plutus-playground-docker = pkgs.dockerTools.buildImage {
      name = "plutus-playground-docker";
      contents = [ plutus-playground-client plutus-server-invoker ];
      config = {
        Cmd = ["${plutus-server-invoker}/bin/plutus-playground-server" "webserver" "-b" "0.0.0.0" "-p" "8080" "${plutus-playground-client}"];
      };
    };
    inherit (pkgs) stack2nix;
  });

in
  # The top-level package set
  pkgs.lib.makeScope pkgs.newScope packages
