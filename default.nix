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

  sources = import ./nix/sources.nix;

  iohkNix = import sources.iohk-nix {
    inherit system config;
    # Make iohk-nix use our nixpkgs
    sourcesOverride = { inherit (sources) nixpkgs; };
  };

  sphinxcontrib-haddock = pkgs.callPackage sources.sphinxcontrib-haddock { pythonPackages = pkgs.python3Packages; };
  sphinx-markdown-tables = pkgs.python3Packages.callPackage ./nix/python/sphinx-markdown-tables.nix {};
  sphinxemoji = pkgs.python3Packages.callPackage ./nix/python/sphinxemoji.nix {};

  pkgsMusl = import ./nix/default.nix {
    inherit config sourcesOverride;
    system = "x86_64-linux";
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
  inherit pkgs sources iohkNix sphinxcontrib-haddock sphinx-markdown-tables;

  python = {
    inherit sphinx-markdown-tables sphinxemoji;
    inherit (sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
  };

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

    project = import ./nix/haskell.nix { inherit (pkgs) lib stdenv pkgs haskell-nix buildPackages; inherit agdaPackages checkMaterialization; };
    # All the packages defined by our project, including dependencies
    packages = project.hsPkgs;
    # Just the packages in the project
    projectPackages =
      pkgs.haskell-nix.haskellLib.selectProjectPackages packages
      # Need to list this manually to work around https://github.com/input-output-hk/haskell.nix/issues/464
      // { inherit (packages) plutus-metatheory; };

    muslProject = import ./nix/haskell.nix { inherit (pkgsMusl) lib stdenv pkgs haskell-nix buildPackages; inherit agdaPackages checkMaterialization; };
    # All the packages defined by our project, built for musl
    muslPackages = muslProject.hsPkgs;

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

  docs = pkgs.recurseIntoAttrs rec {
    site = pkgs.callPackage ./doc {
      inherit (python) sphinxcontrib-haddock sphinxcontrib-domaintools sphinx-markdown-tables sphinxemoji;
      inherit combined-haddock;
      pythonPackages = pkgs.python3Packages;
    };

    plutus-contract = pkgs.callPackage ./plutus-contract/doc { };
    plutus-book = pkgs.callPackage ./plutus-book/doc { };

    plutus-core-spec = pkgs.callPackage ./plutus-core-spec { inherit latex; };
    multi-currency = pkgs.callPackage ./notes/multi-currency { inherit latex; };
    extended-utxo-spec = pkgs.callPackage ./extended-utxo-spec { inherit latex; };
    lazy-machine = pkgs.callPackage ./notes/fomega/lazy-machine { inherit latex; };
    plutus-report = pkgs.callPackage ./notes/plutus-report/default.nix { inherit latex; };
    cost-model-notes = pkgs.callPackage ./notes/cost-model-notes { inherit latex; };

    combined-haddock = let
      haddock-combine = pkgs.callPackage ./nix/haddock-combine.nix { ghc = haskell.project.pkg-set.config.ghc.package; inherit (sphinxcontrib-haddock) sphinxcontrib-haddock; };
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
    unraveling-recursion = pkgs.callPackage ./papers/unraveling-recursion/default.nix { inherit (agdaPackages) agda; inherit latex; };
    system-f-in-agda = pkgs.callPackage ./papers/system-f-in-agda/default.nix { inherit (agdaPackages) agda standard-library; inherit latex; };
    eutxo = pkgs.callPackage ./papers/eutxo/default.nix { inherit latex; };
    utxoma = pkgs.callPackage ./papers/utxoma/default.nix { inherit latex; };
    eutxoma = pkgs.callPackage ./papers/eutxoma/default.nix { inherit latex; };
  };

  web-ghc = 
    let
      web-ghc-server = set-git-rev haskell.packages.web-ghc.components.exes.web-ghc-server;
      runtimeGhc = haskell.packages.ghcWithPackages (ps: [
        ps.playground-common
        ps.plutus-playground-server
        ps.plutus-use-cases
        ps.marlowe
      ]);
    in pkgs.runCommand "web-ghc" { buildInputs = [pkgs.makeWrapper]; } ''
      # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
      mkdir -p $out/bin
      ln -s ${web-ghc-server}/bin/web-ghc-server $out/bin/web-ghc-server
      wrapProgram $out/bin/web-ghc-server \
        --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
        --set GHC_BIN_DIR "${runtimeGhc}/bin" \
        --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
        --set GHC_RTS "-M2G"
    '';

  webCommon = pkgs.lib.cleanSourceWith { 
    filter = pkgs.lib.cleanSourceFilter;
    src = lib.cleanSourceWith {
      filter = (path: type: !(pkgs.lib.elem (baseNameOf path)
                            [".spago" ".spago2nix" "generated" "generated-docs" "output" "dist" "node_modules" ".psci_modules" ".vscode"]));
      src = ./web-common;
    };
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
        inherit easyPS webCommon;
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
    tutorial = docs.site;
    haddock = docs.combined-haddock;
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
        inherit easyPS webCommon;
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
    
    tutorial = docs.marlowe-tutorial;
  });

  marlowe-symbolic-lambda = pkgsMusl.callPackage ./marlowe-symbolic/lambda.nix { haskellPackages = haskell.muslPackages; };
  
  marlowe-playground-lambda = pkgsMusl.callPackage ./marlowe-playground-server/lambda.nix { haskellPackages = haskell.muslPackages; };

  plutus-playground-lambda = pkgsMusl.callPackage ./plutus-playground-server/lambda.nix { haskellPackages = haskell.muslPackages; };

  deployment = pkgs.callPackage ./deployment { 
    inherit marlowe-playground plutus-playground marlowe-symbolic-lambda marlowe-playground-lambda plutus-playground-lambda; 
  };

  inherit (haskell.packages.plutus-scb.components.exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet;

  plutus-scb = pkgs.recurseIntoAttrs (rec {
    server-invoker = set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

    generated-purescript = pkgs.runCommand "plutus-scb-purescript" {} ''
      mkdir $out
      ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
      ${server-invoker}/bin/plutus-scb psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit (sources) nodejs-headers;
        inherit easyPS webCommon;
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
      demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath plutus-scb; scb-exes = haskell.packages.plutus-scb.components.exes; });
            
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
                ps.plutus-core
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

  agdaPackages =
    # The Agda builder needs a derivation with:
    # - The 'agda' executable
    # - The 'agda-mode' executable
    # - A 'version' attribute
    # So we stitch one together here. It doesn't *seem* to need the library interface files,
    # but it seems like they should be there so I added them too.
    let
      haskellNixAgda = haskell.extraPackages.Agda;
      frankenAgda = (pkgs.symlinkJoin {
        name = "agda";
        paths = [
          haskellNixAgda.components.exes.agda
          haskellNixAgda.components.exes.agda-mode
          haskellNixAgda.components.library
        ];
      }) // { version = haskellNixAgda.identifier.version; };
    in pkgs.callPackage ./nix/agda/default.nix { Agda = frankenAgda; };

  dev = import ./nix/dev.nix { inherit pkgs haskell easyPS; };
}
