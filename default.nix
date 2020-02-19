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
, crossSystem ? builtins.currentSystem
 # The nixpkgs configuration file
, config ? { allowUnfreePredicate = (import ./lib.nix {}).unfreePredicate; }

# Use a pinned version nixpkgs.
, pkgs ? (import ./lib.nix { inherit config system; }).pkgs

# Disable running of tests for all local packages.
, forceDontCheck ? false

# Enable profiling for all haskell packages.
# Profiling slows down performance by 50% so we don't enable it by default.
, enableProfiling ? false

# Keeps the debug information for all haskell packages.
, enableDebugging ? false

# Build (but don't run) benchmarks for all local packages.
, enableBenchmarks ? true

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
  latex = pkgs.callPackage ./nix/latex.nix {};
  sources = import ./nix/sources.nix;

  # easy-purescript-nix has some kind of wacky internal IFD
  # usage that breaks the logic that makes source fetchers
  # use native dependencies. This isn't easy to fix, since
  # the only places that need to use native dependencies
  # are deep inside, and we don't want to build the whole
  # thing native. Fortunately, we only want to build the
  # client on Linux, so that's okay. However, it does
  # mean that e.g. we can't build the client dep updating
  # script on Darwin.
  easyPS = pkgs.callPackage sources.easy-purescript-nix {};

  purty = pkgs.callPackage ./purty { };

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
      # We can pass an evaluated version of our packages into
      # iohk-nix, and then we can also get out the compiler
      # so we make sure it uses the same one.
      pkgsGenerated = import ./pkgs { inherit pkgs; };
    in self.callPackage localLib.iohkNix.haskellPackages {
      inherit forceDontCheck enableProfiling
      enableHaddockHydra enableBenchmarks fasterBuild enableDebugging
      customOverlays pkgsGenerated;
      # Broken on vanilla 19.09, require the IOHK fork. Will be abandoned when
      # we go to haskell.nix anyway.
      enablePhaseMetrics = false;
      enableSplitCheck = false;

      filter = localLib.isPlutus;
      requiredOverlay = ./nix/overlays/haskell-overrides.nix;
    };

    localPackages = localLib.getPackages {
      inherit (self) haskellPackages; filter = localLib.isPlutus;
    };

    tests = {
      shellcheck = pkgs.callPackage localLib.iohkNix.tests.shellcheck { inherit src; };
      stylishHaskell = pkgs.callPackage localLib.iohkNix.tests.stylishHaskell {
        inherit (self.haskellPackages) stylish-haskell;
        inherit src;
      };
      purty = pkgs.callPackage ./nix/tests/purty.nix {
        inherit (self.haskellPackages) purty;
        inherit src;
      };
    };

    docs = {
      # this version of asciidoctor is also more recent, although we don't care about the epub bit
      plutus-tutorial = pkgs.callPackage ./plutus-tutorial/doc { };
      plutus-contract = pkgs.callPackage ./plutus-contract/doc { };
      plutus-book = pkgs.callPackage ./plutus-book/doc { };

      plutus-core-spec = pkgs.callPackage ./plutus-core-spec { inherit latex; };
      multi-currency = pkgs.callPackage ./docs/multi-currency { inherit latex; };
      extended-utxo-spec = pkgs.callPackage ./extended-utxo-spec { inherit latex; };
      lazy-machine = pkgs.callPackage ./docs/fomega/lazy-machine { inherit latex; };

      public-combined-haddock = let
        haddock-combine = pkgs.callPackage ./nix/haddock-combine.nix {};
        publicPackages = localLib.getPackages {
          inherit (self) haskellPackages; filter = localLib.isPublicPlutus;
        };
        in haddock-combine {
          hspkgs = builtins.attrValues publicPackages;
          prologue = pkgs.writeTextFile {
            name = "prologue";
            text = "Combined documentation for all the public Plutus libraries.";
        };
      };

      marlowe-tutorial = pkgs.callPackage ./marlowe-tutorial/doc { };
    };

    papers = {
      unraveling-recursion = pkgs.callPackage ./papers/unraveling-recursion { inherit (agdaPackages) Agda; inherit latex; };
      system-f-in-agda = pkgs.callPackage ./papers/system-f-in-agda { inherit (agdaPackages) Agda AgdaStdlib; inherit latex; };
      eutxo = pkgs.callPackage ./papers/eutxo { inherit latex; };
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
          ${server-invoker}/bin/plutus-playground psgenerator $out
        '';

        in
        pkgs.callPackage ./nix/purescript.nix rec {
          inherit easyPS;
          inherit (sources) nodejs-headers;
          psSrc = generated-purescript;
          src = ./plutus-playground-client;
          webCommonPath = ./web-common;
          packageJSON = ./plutus-playground-client/package.json;
          yarnLock = ./plutus-playground-client/yarn.lock;
          yarnNix = ./plutus-playground-client/yarn.nix;
          packages = pkgs.callPackage ./plutus-playground-client/packages.nix {};
          spagoPackages = pkgs.callPackage ./plutus-playground-client/spago-packages.nix {};
          name = (pkgs.lib.importJSON packageJSON).name;
        };
    };

    marlowe-playground = rec {
      playground-exe = set-git-rev haskellPackages.marlowe-playground-server;
      server-invoker = let
        # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskellPackages.ghcWithPackages (ps: [
          haskellPackages.marlowe
          playground-exe
        ]);
      in pkgs.runCommand "marlowe-server-invoker" { buildInputs = [pkgs.makeWrapper]; } ''
        # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${playground-exe}/bin/marlowe-playground-server $out/bin/marlowe-playground
        wrapProgram $out/bin/marlowe-playground \
          --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
          --set GHC_BIN_DIR "${runtimeGhc}/bin" \
          --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
          --set GHC_RTS "-M2G"
      '';

      client = let
        generated-purescript = pkgs.runCommand "marlowe-playground-purescript" {} ''
          mkdir $out
          ${playground-exe}/bin/marlowe-playground-server psgenerator $out
        '';
        in
        pkgs.callPackage ./nix/purescript.nix rec {
          inherit (sources) nodejs-headers;
          inherit easyPS;
          psSrc = generated-purescript;
          src = ./marlowe-playground-client;
          webCommonPath = ./web-common;
          packageJSON = ./marlowe-playground-client/package.json;
          yarnLock = ./marlowe-playground-client/yarn.lock;
          yarnNix = ./marlowe-playground-client/yarn.nix;
          packages = pkgs.callPackage ./marlowe-playground-client/packages.nix {};
          spagoPackages = pkgs.callPackage ./marlowe-playground-client/spago-packages.nix {};
          name = (pkgs.lib.importJSON packageJSON).name;
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
      marlowePlaygroundImage = with marlowe-playground; pkgs.dockerTools.buildImage {
        name = "marlowe-playground";
        contents = [ client server-invoker defaultPlaygroundConfig ];
        config = {
          Cmd = ["${server-invoker}/bin/marlowe-playground" "--config" "${defaultPlaygroundConfig}/etc/playground.yaml" "webserver" "-b" "0.0.0.0" "-p" "8080" "${client}"];
        };
      };

      development = pkgs.dockerTools.buildImage {
        name = "plutus-development";
        contents =
          let runtimeGhc =
                haskellPackages.ghcWithPackages (ps: [
                  haskellPackages.language-plutus-core
                  haskellPackages.plutus-emulator
                  haskellPackages.plutus-wallet-api
                  haskellPackages.plutus-tx
                  haskellPackages.plutus-tx-plugin
                  haskellPackages.plutus-use-cases
                  haskellPackages.plutus-ir
                  haskellPackages.plutus-contract
                ]);
          in  [
                runtimeGhc
                pkgs.binutils-unwrapped
                pkgs.coreutils
                pkgs.bash
                pkgs.git # needed by cabal-install
                haskellPackages.cabal-install
              ];
        config = {
          Cmd = ["bash"];
        };
      };
    };

    plutus-contract = rec {

      # justStaticExecutables results in a much smaller docker image
      # (16MB vs 588MB)
      static = pkgs.haskell.lib.justStaticExecutables;

      pid1 =  static haskellPackages.pid1;
      contract = static haskellPackages.plutus-contract;

      docker = pkgs.dockerTools.buildImage {
          name = "plutus-contract";
          contents = [pid1 contract];
          config = {
            Entrypoint = ["/bin/pid1"];
            Cmd = ["/bin/contract-guessing-game"];
            ExposedPorts = {
              "8080/tcp" = {};
          };
        };
      };
    };

    agdaPackages = rec {
      Agda = haskellPackages.Agda;
      # Override the agda builder code from nixpkgs to use our versions of Agda and Haskell.
      # The Agda version is from our package set, and is newer than the one in nixpkgs.
      agda = pkgs.agda.override { inherit Agda; };

      # We also rely on a newer version of the stdlib
      AgdaStdlib = (pkgs.AgdaStdlib.override {
        # Need to override the builder arguments
        inherit agda; ghcWithPackages = haskellPackages.ghcWithPackages;
      }).overrideAttrs (oldAttrs: rec {
        # Need to override the source this way
        name = "agda-stdlib-${version}";
        version = "1.2";
        src = sources.agda-stdlib;
      });
    };

    marlowe-symbolic-lambda =
      let
        staticHaskellOverlay = import ./nix/overlays/static-haskell.nix { inherit pkgs; };
        # We must use musl because glibc can't do static linking properly
        muslHaskellPackages = (haskellPackages.override (old: {
          pkgsGenerated = pkgs.pkgsMusl.callPackage ./pkgs {};
          customOverlays = old.customOverlays ++ [ staticHaskellOverlay ];
        }));
      in pkgs.pkgsMusl.callPackage ./marlowe-symbolic/lambda.nix { haskellPackages = muslHaskellPackages; };

    metatheory = import ./metatheory {
      inherit (agdaPackages) agda AgdaStdlib;
      inherit (localLib.iohkNix) cleanSourceHaskell;
      inherit pkgs haskellPackages;
    };

    dev = rec {
      packages = localLib.getPackages {
        inherit (self) haskellPackages; filter = name: builtins.elem name [ "cabal-install" "stylish-haskell" "purty" "hlint" ];
      };

      scripts = {
        inherit (localLib) regeneratePackages;

        fixStylishHaskell = pkgs.writeScript "fix-stylish-haskell" ''
          #!${pkgs.runtimeShell}

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

        fixPurty = pkgs.writeScript "fix-purty" ''
          #!${pkgs.runtimeShell}

          ${pkgs.git}/bin/git diff > pre-purty.diff
          ${pkgs.fd}/bin/fd \
            --extension purs \
            --exclude '*/.psc-package/*' \
            --exclude '*/.spago/*' \
            --exclude '*/node_modules/*' \
            --exclude '*/generated/*' \
            --exec ${packages.purty}/bin/purty --write {}
          ${pkgs.git}/bin/git diff > post-purty.diff
          diff pre-purty.diff post-purty.diff > /dev/null
          if [ $? != 0 ]
          then
            echo "Changes by purty have been made. Please commit them."
          else
            echo "No purty changes were made."
          fi
          rm pre-purty.diff post-purty.diff
          exit
        '';

        updateClientDeps = pkgs.writeScript "update-client-deps" ''
          #!${pkgs.runtimeShell}

          set -eou pipefail

          export PATH=${pkgs.stdenv.lib.makeBinPath [
            pkgs.coreutils
            pkgs.git
            pkgs.python
            pkgs.gnumake
            pkgs.gcc
            pkgs.gnused
            pkgs.nodejs-10_x
            pkgs.nodePackages_10_x.node-gyp
            pkgs.yarn
            # yarn2nix won't seem to build on hydra, see
            # https://github.com/moretea/yarn2nix/pull/103
            # I can't figure out how to fix this...
            #pkgs.yarn2nix-moretea.yarn2nix
            easyPS.purs
            easyPS.psc-package
            easyPS.spago
            easyPS.spago2nix
          ]}

          if [ ! -f package.json ]
          then
              echo "package.json not found. Please run this script from the client directory." >&2
              exit 1
          fi

          echo Installing JavaScript Dependencies
          yarn

          echo Generating nix configs.
          yarn2nix > yarn.nix
          spago2nix generate

          echo Done
        '';
      };

      withDevTools = env: env.overrideAttrs (attrs:
        { nativeBuildInputs = attrs.nativeBuildInputs ++
                              [ packages.cabal-install
                                packages.hlint
                                packages.stylish-haskell

                                pkgs.ghcid
                                pkgs.git
                                pkgs.cacert
                                pkgs.yarn
                                pkgs.zlib
                                pkgs.z3
                                pkgs.sqlite-analyzer
                                pkgs.sqlite-interactive

                                easyPS.purs
                                easyPS.spago
                                easyPS.purty
                              ];
        });
    };
  });


in
  # The top-level package set
  pkgs.lib.makeScope pkgs.newScope packages
