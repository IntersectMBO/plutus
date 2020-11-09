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
, sourcesOverride ? { }
  # { pkgs pkgsMusl pkgsLocal }
, packages ? import ./nix { inherit system crossSystem config sourcesOverride rev checkMaterialization; }
  # pinned nixpkgs
, pkgs ? packages.pkgs
  # local packages (./nix/pkgs)
, pkgsLocal ? packages.pkgsLocal
  # musl linked nixpkgs
, pkgsMusl ? packages.pkgsMusl
  # An explicit git rev to use, passed when we are in Hydra
, rev ? null
  # Whether to check that the pinned shas for haskell.nix are correct. We want this to be
  # false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
}:

let
  inherit (pkgs) lib haskell-nix;
  inherit (pkgsLocal) haskell iohkNix git-rev set-git-rev agdaPackages;
  inherit (pkgsLocal) easyPS sphinxcontrib-haddock nodejs-headers;

  # provides `buildLatex` and `filterLatex`
  latex = pkgs.callPackage ./nix/lib/latex.nix { };
in
rec {
  inherit pkgs pkgsLocal pkgsMusl;

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
      inherit (pkgsLocal) sphinx-markdown-tables sphinxemoji;
      inherit (sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
      inherit combined-haddock;
      pythonPackages = pkgs.python3Packages;
    };

    plutus-contract = pkgs.callPackage ./plutus-contract/doc { };
    plutus-core-spec = pkgs.callPackage ./plutus-core-spec { inherit latex; };
    multi-currency = pkgs.callPackage ./notes/multi-currency { inherit latex; };
    extended-utxo-spec = pkgs.callPackage ./extended-utxo-spec { inherit latex; };
    lazy-machine = pkgs.callPackage ./notes/fomega/lazy-machine { inherit latex; };
    plutus-report = pkgs.callPackage ./notes/plutus-report/default.nix { inherit latex; };
    cost-model-notes = pkgs.callPackage ./notes/cost-model-notes { inherit latex; };

    combined-haddock =
      let
        toHaddock = haskell-nix.haskellLib.collectComponents' "library" haskell.projectPackages;
        haddock-combine = pkgs.callPackage ./nix/lib/haddock-combine.nix {
          ghc = haskell.project.pkg-set.config.ghc.package;
          inherit (sphinxcontrib-haddock) sphinxcontrib-haddock;
        };
      in
      haddock-combine {
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
    in
    pkgs.runCommand "web-ghc" { buildInputs = [ pkgs.makeWrapper ]; } ''
      # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
      mkdir -p $out/bin
      ln -s ${web-ghc-server}/bin/web-ghc-server $out/bin/web-ghc-server
      wrapProgram $out/bin/web-ghc-server \
        --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
        --set GHC_BIN_DIR "${runtimeGhc}/bin" \
        --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
        --set GHC_RTS "-M2G"
    '';

  webCommon = lib.cleanSourceWith {
    filter = lib.cleanSourceFilter;
    src = lib.cleanSourceWith {
      filter = (path: type: !(lib.elem (baseNameOf path)
        [ ".spago" ".spago2nix" "generated" "generated-docs" "output" "dist" "node_modules" ".psci_modules" ".vscode" ]));
      src = ./web-common;
    };
  };

  plutus-playground = pkgs.recurseIntoAttrs (rec {
    playground-exe = set-git-rev haskell.packages.plutus-playground-server.components.exes.plutus-playground-server;
    server-invoker =
      let
        # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskell.packages.ghcWithPackages (ps: [
          ps.playground-common
          ps.plutus-playground-server
          ps.plutus-use-cases
        ]);
      in
      pkgs.runCommand "plutus-server-invoker" { buildInputs = [ pkgs.makeWrapper ]; } ''
        # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${playground-exe}/bin/plutus-playground-server $out/bin/plutus-playground
        wrapProgram $out/bin/plutus-playground \
          --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
          --set GHC_BIN_DIR "${runtimeGhc}/bin" \
          --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
          --set GHC_RTS "-M2G"
      '';

    generated-purescript = pkgs.runCommand "plutus-playground-purescript" { } ''
      mkdir $out
      ${server-invoker}/bin/plutus-playground psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit nodejs-headers;
        inherit easyPS webCommon;
        psSrc = generated-purescript;
        src = ./plutus-playground-client;
        packageJSON = ./plutus-playground-client/package.json;
        yarnLock = ./plutus-playground-client/yarn.lock;
        yarnNix = ./plutus-playground-client/yarn.nix;
        additionalPurescriptSources = [ "../web-common/**/*.purs" ];
        packages = pkgs.callPackage ./plutus-playground-client/packages.nix { };
        spagoPackages = pkgs.callPackage ./plutus-playground-client/spago-packages.nix { };
        name = (pkgs.lib.importJSON packageJSON).name;
        checkPhase = ''node -e 'require("./output/Test.Main").main()' '';
      };
    tutorial = docs.site;
    haddock = docs.combined-haddock;
  });

  marlowe-playground = pkgs.recurseIntoAttrs (rec {
    playground-exe = set-git-rev haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server;
    server-invoker =
      let
        # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
        runtimeGhc = haskell.packages.ghcWithPackages (ps: [
          ps.marlowe
          ps.marlowe-playground-server
        ]);
      in
      pkgs.runCommand "marlowe-server-invoker" { buildInputs = [ pkgs.makeWrapper ]; } ''
        # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
        mkdir -p $out/bin
        ln -s ${playground-exe}/bin/marlowe-playground-server $out/bin/marlowe-playground
        wrapProgram $out/bin/marlowe-playground \
          --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
          --set GHC_BIN_DIR "${runtimeGhc}/bin" \
          --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
          --set GHC_RTS "-M2G"
      '';

    generated-purescript = pkgs.runCommand "marlowe-playground-purescript" { } ''
      mkdir $out
      ${playground-exe}/bin/marlowe-playground-server psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit nodejs-headers;
        inherit easyPS webCommon;
        psSrc = generated-purescript;
        src = ./marlowe-playground-client;
        packageJSON = ./marlowe-playground-client/package.json;
        yarnLock = ./marlowe-playground-client/yarn.lock;
        yarnNix = ./marlowe-playground-client/yarn.nix;
        additionalPurescriptSources = [ "../web-common/**/*.purs" ];
        packages = pkgs.callPackage ./marlowe-playground-client/packages.nix { };
        spagoPackages = pkgs.callPackage ./marlowe-playground-client/spago-packages.nix { };
        name = (pkgs.lib.importJSON packageJSON).name;
      };

    tutorial = docs.marlowe-tutorial;
  });

  marlowe-symbolic-lambda = pkgsMusl.callPackage ./marlowe-symbolic/lambda.nix { haskellPackages = haskell.muslPackages; };

  marlowe-playground-lambda = pkgsMusl.callPackage ./marlowe-playground-server/lambda.nix { haskellPackages = haskell.muslPackages; };

  plutus-playground-lambda = pkgsMusl.callPackage ./plutus-playground-server/lambda.nix { haskellPackages = haskell.muslPackages; };

  deployment = pkgs.callPackage ./deployment {
    inherit pkgsLocal marlowe-playground plutus-playground marlowe-symbolic-lambda marlowe-playground-lambda plutus-playground-lambda;
  };

  inherit (haskell.packages.plutus-scb.components.exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet;

  plutus-scb = pkgs.recurseIntoAttrs (rec {
    server-invoker = set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

    generated-purescript = pkgs.runCommand "plutus-scb-purescript" { } ''
      mkdir $out
      ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
      ${server-invoker}/bin/plutus-scb psgenerator $out
    '';

    client =
      pkgs.callPackage ./nix/purescript.nix rec {
        inherit nodejs-headers;
        inherit easyPS webCommon;
        psSrc = generated-purescript;
        src = ./plutus-scb-client;
        packageJSON = ./plutus-scb-client/package.json;
        yarnLock = ./plutus-scb-client/yarn.lock;
        yarnNix = ./plutus-scb-client/yarn.nix;
        additionalPurescriptSources = [ "../web-common/**/*.purs" ];
        packages = pkgs.callPackage ./plutus-scb-client/packages.nix { };
        spagoPackages = pkgs.callPackage ./plutus-scb-client/spago-packages.nix { };
        name = (pkgs.lib.importJSON packageJSON).name;
        checkPhase = ''node -e 'require("./output/Test.Main").main()' '';
      };
    demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath plutus-scb; scb-exes = haskell.packages.plutus-scb.components.exes; });

  });

  docker = import ./nix/docker.nix {
    inherit (pkgs) dockerTools binutils-unwrapped coreutils bash git cabal-install writeTextFile;
    inherit plutus-playground marlowe-playground haskell;
  };
}
