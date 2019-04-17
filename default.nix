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

# An explicit git rev to use, passed when we are in Hydra
, rev ? null

}:

with pkgs.lib;

let
  localLib = import ./lib.nix { inherit config system; } ;
  src = localLib.iohkNix.cleanSourceHaskell ./.;

  # We have to use purescript 0.11.7 - because purescript-bridge
  # hasn't been updated for 0.12 yet - but our pinned nixpkgs
  # has 0.12, and overriding doesn't work easily because we
  # can't built 0.11.7 with the default compiler either.
  purescriptNixpkgs = import (localLib.iohkNix.fetchNixpkgs ./purescript-11-nixpkgs-src.json) {};


  packages = self: (rec {
    inherit pkgs localLib;

    # The git revision comes from `rev` if available (Hydra), otherwise
    # it is read using IFD and git, which is avilable on local builds.
    # NOTE: depending on this will make your package rebuild on every commit, regardless of whether
    # anything else has changed!
    git-rev = 
      let ifdRev = (import (pkgs.callPackage ./nix/git-rev.nix { gitDir = builtins.path { name = "gitDir"; path = ./.git; }; })).rev;
      in removeSuffix "\n" (if isNull rev then ifdRev else rev);

    # This is the stackage LTS plus overrides, plus the plutus
    # packages.
    haskellPackages = let
      errorOverlay = import ./nix/overlays/force-error.nix {
        inherit pkgs;
        filter = localLib.isPlutus;
      };
      # When building we want the git sha available in the Haskell code, previously we did this with
      # a template haskell function that ran a git command however the git directory is not available
      # to the derivation so this fails. What we do now is create a derivation that overrides a magic
      # Haskell module with the git sha.
      gitModuleOverlay = import ./nix/overlays/git-module.nix {
        inherit pkgs git-rev;
      };
      customOverlays = optional forceError errorOverlay ++ [gitModuleOverlay];
      # Filter down to local packages, except those named in the given list
      localButNot = nope:
        let okay = builtins.filter (name: !(builtins.elem name nope)) localLib.plutusPkgList;
        in name: builtins.elem name okay;
      # We can pass an evaluated version of our packages into
      # iohk-nix, and then we can also get out the compiler
      # so we make sure it uses the same one.
      pkgsGenerated = import ./pkgs { inherit pkgs; };
    in self.callPackage localLib.iohkNix.haskellPackages {
      inherit forceDontCheck enableProfiling enablePhaseMetrics
      enableHaddockHydra enableBenchmarks fasterBuild enableDebugging
      enableSplitCheck customOverlays pkgsGenerated;

      filter = localLib.isPlutus;
      filterOverrides = {
        splitCheck = localButNot [
            # Broken for things with test tool dependencies
            "wallet-api"
            "plutus-tx"
            "plutus-tutorial"
            # Broken for things which pick up other files at test runtime
            "plutus-playground-server"
            "meadow"
          ];
        haddock = localButNot [
            # Haddock is broken for things with internal libraries
            "plutus-tx"

            # Also broken for the sample contracts that are put in a docker
            # image (cf. plutus-contract-exe.docker below)
            "plutus-contract-exe"
        ];
      };
      requiredOverlay = ./nix/overlays/required.nix;
    };

    localPackages = localLib.getPackages {
      inherit (self) haskellPackages; filter = localLib.isPlutus;
    };

    tests = {
      shellcheck = pkgs.callPackage localLib.iohkNix.tests.shellcheck { inherit src; };
      hlint = pkgs.callPackage localLib.iohkNix.tests.hlint {
        inherit src;
        projects = localLib.plutusHaskellPkgList;
      };
      stylishHaskell = pkgs.callPackage localLib.iohkNix.tests.stylishHaskell {
        inherit (self.haskellPackages) stylish-haskell;
        inherit src;
      };
    };

    docs = {
      plutus-core-spec = pkgs.callPackage ./plutus-core-spec {};
      lazy-machine = pkgs.callPackage ./docs/fomega/lazy-machine {};
      combined-haddock = (pkgs.callPackage ./nix/haddock-combine.nix {}) {
        hspkgs = builtins.attrValues localPackages;
        prologue = pkgs.writeTextFile {
          name = "prologue";
          text = "Combined documentation for all the Plutus libraries.";
        };
      };
    };

    plutus-playground = rec {
      server-invoker = let
        # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskellPackages.ghcWithPackages (ps: [
          haskellPackages.plutus-playground-server
          haskellPackages.plutus-playground-lib
          haskellPackages.plutus-use-cases
        ]);
      in pkgs.runCommand "plutus-server-invoker" { buildInputs = [pkgs.makeWrapper]; } ''
        # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${haskellPackages.plutus-playground-server}/bin/plutus-playground-server $out/bin/plutus-playground
        wrapProgram $out/bin/plutus-playground \
          --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
          --set GHC_BIN_DIR "${runtimeGhc}/bin" \
          --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
          --set GHC_RTS "-M2G"
      '';

      client = let
        generated-purescript = pkgs.runCommand "plutus-playground-purescript" {} ''
          mkdir $out
          ${haskellPackages.plutus-playground-server}/bin/plutus-playground-server psgenerator $out
        '';
        in
        pkgs.callPackage ./plutus-playground-client {
          pkgs = purescriptNixpkgs;
          psSrc = generated-purescript;
        };

    };

    meadow = rec {
      server-invoker = let
        # meadow uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskellPackages.ghcWithPackages (ps: [
          haskellPackages.marlowe
          haskellPackages.meadow
        ]);
      in pkgs.runCommand "meadow-server-invoker" { buildInputs = [pkgs.makeWrapper]; } ''
        # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${haskellPackages.meadow}/bin/meadow-exe $out/bin/meadow
        wrapProgram $out/bin/meadow \
          --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
          --set GHC_BIN_DIR "${runtimeGhc}/bin" \
          --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
          --set GHC_RTS "-M2G"
      ''; 

      client = let
        generated-purescript = pkgs.runCommand "meadow-purescript" {} ''
          mkdir $out
          ${haskellPackages.meadow}/bin/meadow-exe psgenerator $out
        '';
        in
        pkgs.callPackage ./meadow-client {
          pkgs = purescriptNixpkgs;
          psSrc = generated-purescript;
        };
    };

    docker = rec {
      defaultPlaygroundConfig = pkgs.writeTextFile {
        name = "playground.yaml";
        destination = "/etc/playground.yaml";
        text = ''
        auth:
          github-client-id: ""
          github-client-secret: ""
          jwt-signature: ""
          redirect-url: "localhost:8080"
        '';
      };
      plutusPlaygroundImage = with plutus-playground; pkgs.dockerTools.buildImage {
        name = "plutus-playgrounds";
        contents = [ client server-invoker defaultPlaygroundConfig ];
        config = {
          Cmd = ["${server-invoker}/bin/plutus-playground" "--config" "${defaultPlaygroundConfig}/etc/playground.yaml" "webserver" "-b" "0.0.0.0" "-p" "8080" "${client}"];
        };
      };
      meadowImage = with meadow; pkgs.dockerTools.buildImage {
        name = "meadow";
        contents = [ client server-invoker defaultPlaygroundConfig ];
        config = {
          Cmd = ["${server-invoker}/bin/meadow" "--config" "${defaultPlaygroundConfig}/etc/playground.yaml" "webserver" "-b" "0.0.0.0" "-p" "8080" "${client}"];
        };
      };
    };

    plutus-contract-exe = rec {

      # justStaticExecutables results in a much smaller docker image
      # (16MB vs 588MB)
      static = pkgs.haskell.lib.justStaticExecutables;

      pid1 =  static haskellPackages.pid1;
      contract = static haskellPackages.plutus-contract-exe;

      docker = pkgs.dockerTools.buildImage {
          name = "plutus-contract-exe";
          contents = [pid1 contract];
          config = {
            Entrypoint = ["/bin/pid1"];
            Cmd = ["/bin/contract-exe-guessing-game"];
            ExposedPorts = {
              "8080/tcp" = {};
          };
        };
      };
    };

    dev = rec {
      packages = localLib.getPackages {
        inherit (self) haskellPackages; filter = name: builtins.elem name [ "cabal-install" "stylish-haskell" ];
      };
      scripts = {
        inherit (localLib) regeneratePackages;

        fixStylishHaskell = pkgs.writeScript "fix-stylish-haskell" ''
          ${pkgs.git}/bin/git diff > pre-stylish.diff
          ${pkgs.fd}/bin/fd \
            --extension hs \
            --exclude '*/dist/*' \
            --exclude '*/docs/*' \
            --exec ${packages.stylish-haskell}/bin/stylish-haskell -i {}
          ${pkgs.git}/bin/git diff > post-stylish.diff
          diff pre-stylish.diff post-stylish.diff > /dev/null
          if [ $? != 0 ]
          then
            echo "Changes by stylish have been made. Please commit them."
          else
            echo "No stylish changes were made."
          fi
          rm pre-stylish.diff post-stylish.diff
          exit
        '';
      };

      withDevTools = env: env.overrideAttrs (attrs: { nativeBuildInputs = attrs.nativeBuildInputs ++ [ packages.cabal-install ]; });
    };
      
    shellTemplate = name: dev.withDevTools haskellPackages."${name}".env;
  });


in
  # The top-level package set
  pkgs.lib.makeScope pkgs.newScope packages
