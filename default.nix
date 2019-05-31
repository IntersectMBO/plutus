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

  pp2nSrc = pkgs.fetchFromGitHub {
    owner = "justinwoo";
    repo = "psc-package2nix";
    rev = "6e8f6dc6dea896c71b30cc88a2d95d6d1e48a6f0";
    sha256 = "0fa6zaxxmqxva1xmnap9ng7b90zr9a55x1l5xk8igdw2nldqfa46";
  };

  yarn2nixSrc = pkgs.fetchFromGitHub {
    owner = "moretea";
    repo = "yarn2nix";
    rev = "780e33a07fd821e09ab5b05223ddb4ca15ac663f";
    sha256 = "1f83cr9qgk95g3571ps644rvgfzv2i4i7532q8pg405s4q5ada3h";
  };

  pp2n = import pp2nSrc { inherit pkgs; };
  yarn2nix = import yarn2nixSrc { inherit pkgs; };

  packages = self: (rec {
    inherit pkgs localLib;

    # The git revision comes from `rev` if available (Hydra), otherwise
    # it is read using IFD and git, which is avilable on local builds.
    git-rev = if isNull rev then localLib.iohkNix.commitIdFromGitRepo ./.git else rev;

    # set-git-rev is a function that can be called on a haskellPackages package to inject the git revision post-compile
    set-git-rev = self.callPackage ./scripts/set-git-rev {
      inherit (self.haskellPackages) ghc;
      inherit git-rev;
    };

    # This is the stackage LTS plus overrides, plus the plutus
    # packages.
    haskellPackages = let
      errorOverlay = import ./nix/overlays/force-error.nix {
        inherit pkgs;
        filter = localLib.isPlutus;
      };
      customOverlays = optional forceError errorOverlay;
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
            "plutus-wallet-api"
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
      extended-utxo-spec = pkgs.callPackage ./extended-utxo-spec {};
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
      playground-exe = set-git-rev haskellPackages.plutus-playground-server;
      server-invoker = let
        # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskellPackages.ghcWithPackages (ps: [
          playground-exe
          haskellPackages.plutus-playground-lib
          haskellPackages.plutus-use-cases
        ]);
      in pkgs.runCommand "plutus-server-invoker" { buildInputs = [pkgs.makeWrapper]; } ''
        # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${playground-exe}/bin/plutus-playground-server $out/bin/plutus-playground
        wrapProgram $out/bin/plutus-playground \
          --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
          --set GHC_BIN_DIR "${runtimeGhc}/bin" \
          --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
          --set GHC_RTS "-M2G"
      '';

      client = let
        generated-purescript = pkgs.runCommand "plutus-playground-purescript" {} ''
          mkdir $out
          ${playground-exe}/bin/plutus-playground-server psgenerator $out
        '';
        in
        pkgs.callPackage ./plutus-playground-client {
          inherit pkgs yarn2nix pp2nSrc haskellPackages;
          psSrc = generated-purescript;
        };
    };

    meadow = rec {
      meadow-exe = set-git-rev haskellPackages.meadow;
      server-invoker = let
        # meadow uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskellPackages.ghcWithPackages (ps: [
          haskellPackages.marlowe
          meadow-exe
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
          ${meadow-exe}/bin/meadow-exe psgenerator $out
        '';
        in
        pkgs.callPackage ./meadow-client {
          inherit pkgs yarn2nix pp2nSrc haskellPackages;
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

    agdaPackages = rec {
      # Override the agda builder code from nixpkgs to use our versions of Agda and Haskell.
      # The Agda version is from our package set, and is newer than the one in nixpkgs.
      agda = pkgs.agda.override { Agda = haskellPackages.Agda; };

      # We also rely on a newer version of the stdlib
      AgdaStdlib = (pkgs.AgdaStdlib.override { 
        # Need to override the builder arguments
        inherit agda; ghcWithPackages = haskellPackages.ghcWithPackages; 
      }).overrideAttrs (oldAttrs: rec {
        # Need to override the source this way
        name = "agda-stdlib-${version}";
        version = "1.0.1";
        src = pkgs.fetchFromGitHub {
          owner = "agda";
          repo = "agda-stdlib";
          rev = "v1.0.1";
          sha256 = "0ia7mgxs5g9849r26yrx07lrx65vhlrxqqh5b6d69gfi1pykb4j2";
        };
      });
    };

    metatheory = import ./metatheory { 
      inherit (agdaPackages) agda AgdaStdlib; 
      inherit (localLib.iohkNix) cleanSourceHaskell; 
      inherit pkgs haskellPackages; 
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

        updateClientDeps = pkgs.writeScript "update-client-deps" ''
          if [ ! -f package.json ]
          then
              echo "package.json not found. Please run this script from the client directory." >&2
              exit 1
          fi

          echo Installing JavaScript Dependencies
          ${pkgs.yarn}/bin/yarn
          echo Generating psc-package config
          ${pkgs.yarn}/bin/yarn spago psc-package-insdhall
          echo Installing PureScript Dependencies
          ${pkgs.yarn}/bin/yarn psc-package install
          echo Generating nix config
          ${pp2n}/bin/pp2n psc-package2nix
          ${yarn2nix.yarn2nix}/bin/yarn2nix > yarn.nix
          cp .psc-package/local/.set/packages.json packages.json
          echo Done
        '';
      };

      withDevTools = env: env.overrideAttrs (attrs: { nativeBuildInputs = attrs.nativeBuildInputs ++ [ packages.cabal-install ]; });
    };
      
    shellTemplate = name: dev.withDevTools haskellPackages."${name}".env;
  });


in
  # The top-level package set
  pkgs.lib.makeScope pkgs.newScope packages
