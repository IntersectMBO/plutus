########################################################################
# default.nix -- The top-level nix build file for Plutus.
#
# This file defines various attributes that are used for building and
# developing Plutus.
#
########################################################################

{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; }

# Overrides for niv
, sourcesOverride ? {}
# Nixpkgs override
, pkgs ? import ./nix/default.nix { inherit system crossSystem config sourcesOverride; }

# An explicit git rev to use, passed when we are in Hydra
, rev ? null
# Whether to check that the pinned shas for haskell.nix are correct. We want this to be
# false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
}:


let
  inherit (pkgs) lib;
  localLib = import ./lib.nix;

  sources = import ./nix/sources.nix;

  iohkNix = import sources.iohk-nix {
    inherit system config;
    # Make iohk-nix use our nixpkgs
    sourcesOverride = { inherit (sources) nixpkgs; };
  };

  pkgsMusl = import ./nix/default.nix {
    inherit system config sourcesOverride;
    crossSystem = lib.systems.examples.musl64;
  };

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

in rec {
  inherit pkgs localLib iohkNix;

  # The git revision comes from `rev` if available (Hydra), otherwise
  # it is read using IFD and git, which is avilable on local builds.
  git-rev = if isNull rev then iohkNix.commitIdFromGitRepo ./.git else rev;

  # set-git-rev is a function that can be called on a haskellPackages package to inject the git revision post-compile
  set-git-rev = pkgs.callPackage ./scripts/set-git-rev/default.nix {
    inherit (haskell.packages) ghcWithPackages;
    inherit git-rev;
  };

  latex = pkgs.callPackage ./nix/latex.nix {};

  haskell = rec {
    # The Hackage index-state from cabal.project
    index-state =
      let
        # Borrowed from haskell.nix
        parseIndexState = rawCabalProject:
            let
              indexState = pkgs.lib.lists.concatLists (
                pkgs.lib.lists.filter (l: l != null)
                  (builtins.map (l: builtins.match "^index-state: *(.*)" l)
                    (pkgs.lib.splitString "\n" rawCabalProject)));
            in pkgs.lib.lists.head (indexState ++ [ null ]);
      in parseIndexState (builtins.readFile ./cabal.project);

    # All the packages defined by our project, including dependencies
    packages = import ./nix/haskell.nix { inherit (pkgs) lib stdenv pkgs haskell-nix buildPackages; inherit metatheory checkMaterialization; };
    # Just the packages in the project
    projectPackages =
      pkgs.haskell-nix.haskellLib.selectProjectPackages packages
      # Need to list this manually to work around https://github.com/input-output-hk/haskell.nix/issues/464
      // { inherit (packages) plc-agda; };
    # All the packages defined by our project, built for musl
    muslPackages = import ./nix/haskell.nix { inherit (pkgsMusl) lib stdenv pkgs haskell-nix buildPackages; inherit metatheory checkMaterialization; };
    # Extra Haskell packages which we use but aren't part of the main project definition.
    extraPackages = pkgs.callPackage ./nix/haskell-extra.nix { inherit index-state checkMaterialization; };
  };

  tests = import ./nix/tests/default.nix {
    inherit pkgs iohkNix haskell;
    # Just do some basic cleaning here, the tests do more
    src = lib.cleanSourceWith {
      filter = lib.cleanSourceFilter;
      src = ./.;
      # Otherwise this depends on the name in the parent directory, which reduces caching, and is
      # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
      name = "plutus";
    };
  };

  docs = pkgs.recurseIntoAttrs {
    plutus-tutorial = pkgs.callPackage ./plutus-tutorial/doc { };
    plutus-contract = pkgs.callPackage ./plutus-contract/doc { };
    plutus-book = pkgs.callPackage ./plutus-book/doc { };

    plutus-core-spec = pkgs.callPackage ./plutus-core-spec { inherit latex; };
    multi-currency = pkgs.callPackage ./docs/multi-currency { inherit latex; };
    extended-utxo-spec = pkgs.callPackage ./extended-utxo-spec { inherit latex; };
    lazy-machine = pkgs.callPackage ./docs/fomega/lazy-machine { inherit latex; };
    plutus-report = pkgs.callPackage ./docs/plutus-report/default.nix { inherit latex; };

    combined-haddock = let
      haddock-combine = pkgs.callPackage ./nix/haddock-combine.nix {};
      toHaddock = pkgs.haskell-nix.haskellLib.collectComponents' "library" haskell.projectPackages;
      in haddock-combine {
        hspkgs = builtins.attrValues toHaddock;
        prologue = pkgs.writeTextFile {
          name = "prologue";
          text = "Combined documentation for all the public Plutus libraries.";
      };
    };

    marlowe-tutorial = pkgs.callPackage ./marlowe/doc { };
  };

  papers = pkgs.recurseIntoAttrs {
    unraveling-recursion = pkgs.callPackage ./papers/unraveling-recursion/default.nix { inherit (agdaPackages) Agda; inherit latex; };
    system-f-in-agda = pkgs.callPackage ./papers/system-f-in-agda/default.nix { inherit (agdaPackages) Agda AgdaStdlib; inherit latex; };
    eutxo = pkgs.callPackage ./papers/eutxo/default.nix { inherit latex; };
  };

  plutus-playground = pkgs.recurseIntoAttrs (rec {
    playground-exe = set-git-rev haskell.packages.plutus-playground-server.components.exes.plutus-playground-server;
    server-invoker = let
      # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
      runtimeGhc = haskell.packages.ghcWithPackages (ps: [
        ps.playground-common
        ps.plutus-playground-server
        ps.plutus-use-cases
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

    generated-purescript = pkgs.runCommand "plutus-playground-purescript" {} ''
      mkdir $out
      ${server-invoker}/bin/plutus-playground psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit (sources) nodejs-headers;
        inherit easyPS;
        psSrc = generated-purescript;
        src = ./plutus-playground-client;
        packageJSON = ./plutus-playground-client/package.json;
        yarnLock = ./plutus-playground-client/yarn.lock;
        yarnNix = ./plutus-playground-client/yarn.nix;
        additionalPurescriptSources = [ "../web-common/**/*.purs" ];
        packages = pkgs.callPackage ./plutus-playground-client/packages.nix {};
        spagoPackages = pkgs.callPackage ./plutus-playground-client/spago-packages.nix {};
        name = (pkgs.lib.importJSON packageJSON).name;
        checkPhase = ''node -e 'require("./output/Test.Main").main()' '';
      };
  });

  marlowe-playground = pkgs.recurseIntoAttrs (rec {
    playground-exe = set-git-rev haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server;
    server-invoker = let
      # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
      runtimeGhc = haskell.packages.ghcWithPackages (ps: [
        ps.marlowe
        ps.marlowe-playground-server
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

    generated-purescript = pkgs.runCommand "marlowe-playground-purescript" {} ''
      mkdir $out
      ${playground-exe}/bin/marlowe-playground-server psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit (sources) nodejs-headers;
        inherit easyPS;
        psSrc = generated-purescript;
        src = ./marlowe-playground-client;
        packageJSON = ./marlowe-playground-client/package.json;
        yarnLock = ./marlowe-playground-client/yarn.lock;
        yarnNix = ./marlowe-playground-client/yarn.nix;
        additionalPurescriptSources = [ "../web-common/**/*.purs" ];
        packages = pkgs.callPackage ./marlowe-playground-client/packages.nix {};
        spagoPackages = pkgs.callPackage ./marlowe-playground-client/spago-packages.nix {};
        name = (pkgs.lib.importJSON packageJSON).name;
      };
  });

  plutus-scb = pkgs.recurseIntoAttrs (rec {
    server-invoker= set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

    generated-purescript = pkgs.runCommand "plutus-scb-purescript" {} ''
      mkdir $out
      ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
      ${server-invoker}/bin/plutus-scb psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit (sources) nodejs-headers;
        inherit easyPS;
        psSrc = generated-purescript;
        src = ./plutus-scb-client;
        packageJSON = ./plutus-scb-client/package.json;
        yarnLock = ./plutus-scb-client/yarn.lock;
        yarnNix = ./plutus-scb-client/yarn.nix;
        additionalPurescriptSources = [ "../web-common/**/*.purs" ];
        packages = pkgs.callPackage ./plutus-scb-client/packages.nix {};
        spagoPackages = pkgs.callPackage ./plutus-scb-client/spago-packages.nix {};
        name = (pkgs.lib.importJSON packageJSON).name;
        checkPhase = ''node -e 'require("./output/Test.Main").main()' '';
      };
  });

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
              haskell.packages.ghcWithPackages (ps: [
                ps.language-plutus-core
                ps.plutus-ledger
                ps.plutus-tx
                ps.plutus-tx-plugin
                ps.plutus-use-cases
                ps.plutus-contract
              ]);
        in  [
              runtimeGhc
              pkgs.binutils-unwrapped
              pkgs.coreutils
              pkgs.bash
              pkgs.git # needed by cabal-install
              pkgs.cabal-install
            ];
      config = {
        Cmd = ["bash"];
      };
    };
  };

  agdaPackages = rec {
    # We can use Agda from nixpkgs for the moment, we may need to change this again
    # if we want to move to a more recent version.
    Agda = pkgs.haskellPackages.Agda;
    agda = pkgs.agda;

    # We also rely on a newer version of the stdlib
    AgdaStdlib = pkgs.AgdaStdlib.overrideAttrs (oldAttrs: rec {
      # Need to override the source this way
      name = "agda-stdlib-${version}";
      version = "1.2";
      src = sources.agda-stdlib;
      # Marked as broken on darwin in our nixpkgs, but not actually broken,
      # fixed in https://github.com/NixOS/nixpkgs/pull/76485 but we don't have that yet
      meta = oldAttrs.meta // { broken = false; };
    });
  };

  marlowe-symbolic-lambda = pkgsMusl.callPackage ./marlowe-symbolic/lambda.nix { haskellPackages = haskell.muslPackages; };

  metatheory = import ./metatheory/default.nix {
    inherit (agdaPackages) agda AgdaStdlib;
    inherit (pkgs.haskell-nix) cleanSourceHaskell;
    inherit (pkgs) lib;
  };

  dev = import ./nix/dev.nix { inherit pkgs haskell easyPS; };
}
